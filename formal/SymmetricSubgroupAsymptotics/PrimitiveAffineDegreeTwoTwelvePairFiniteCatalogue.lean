import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueAssemblyRows251To301

/-! Generated literal count-twelve pair-top catalogue from the pinned
action/module alphabet.  Completeness of each registry is semantic. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelvePairFiniteCatalogue

private def pairedSix1Generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 3, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 0, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix1Generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 3, 2, 1, 5, 4] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 3, 2, 1, 5, 4] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix1Generator2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairedSix1Generators : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairedSix1Generator0, pairedSix1Generator1, pairedSix1Generator2]

abbrev PairedSix1Top : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure (Set.range pairedSix1Generators)

noncomputable def pairedSix1Interface : DegreeTwoPairTopFiniteInterface 6 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    PairedSix1Top

private def pairedSix2Generator0 : Equiv.Perm (Fin 6) where
  toFun x := (#[1, 3, 2, 0, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[3, 0, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix2Generator1 : Equiv.Perm (Fin 6) where
  toFun x := (#[0, 3, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  invFun x := (#[0, 3, 2, 1, 4, 5] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def pairedSix2Generator2 : Equiv.Perm (Fin 6) where
  toFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  invFun x := (#[2, 4, 0, 5, 1, 3] : Array (Fin 6))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairedSix2Generators : Fin 3 → Equiv.Perm (Fin 6) :=
  ![pairedSix2Generator0, pairedSix2Generator1, pairedSix2Generator2]

abbrev PairedSix2Top : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure (Set.range pairedSix2Generators)

noncomputable def pairedSix2Interface : DegreeTwoPairTopFiniteInterface 6 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries
    PairedSix2Top

def branch : Fin 301 → DegreeTwoTwelvePairTopBranch :=
  Fin.addCases (m := 50) (n := 251) branchRows1To50 <|
    Fin.addCases (m := 50) (n := 201) branchRows51To100 <|
      Fin.addCases (m := 50) (n := 151) branchRows101To150 <|
        Fin.addCases (m := 50) (n := 101) branchRows151To200 <|
          Fin.addCases (m := 50) (n := 51) branchRows201To250
            branchRows251To301

def kappa : Fin 301 → ℕ :=
  Fin.addCases (m := 50) (n := 251) kappaRows1To50 <|
    Fin.addCases (m := 50) (n := 201) kappaRows51To100 <|
      Fin.addCases (m := 50) (n := 151) kappaRows101To150 <|
        Fin.addCases (m := 50) (n := 101) kappaRows151To200 <|
          Fin.addCases (m := 50) (n := 51) kappaRows201To250
            kappaRows251To301

def sectionCap : Fin 301 → ℕ :=
  Fin.addCases (m := 50) (n := 251) sectionCapRows1To50 <|
    Fin.addCases (m := 50) (n := 201) sectionCapRows51To100 <|
      Fin.addCases (m := 50) (n := 151) sectionCapRows101To150 <|
        Fin.addCases (m := 50) (n := 101) sectionCapRows151To200 <|
          Fin.addCases (m := 50) (n := 51) sectionCapRows201To250
            sectionCapRows251To301

/-- Every generated joint row uses one of the six certified
`(kappa, sectionCap)` pairs. -/
theorem joint_parameters (j : Fin 301) (h : branch j = .joint) :
    (kappa j, sectionCap j) ∈ degreeTwoTwelvePairJointParameters := by
  revert h
  native_decide +revert

noncomputable def finiteInterface : Fin 301 → DegreeTwoPairTopFiniteInterface 12 :=
  Fin.addCases (m := 50) (n := 251) finiteInterfaceRows1To50 <|
    Fin.addCases (m := 50) (n := 201) finiteInterfaceRows51To100 <|
      Fin.addCases (m := 50) (n := 151) finiteInterfaceRows101To150 <|
        Fin.addCases (m := 50) (n := 101) finiteInterfaceRows151To200 <|
          Fin.addCases (m := 50) (n := 51) finiteInterfaceRows201To250
            finiteInterfaceRows251To301

noncomputable def row (j : Fin 301) : DegreeTwoTwelvePairTopRow where
  finite := finiteInterface j
  branch := branch j
  kappa := kappa j
  sectionCap := sectionCap j
  expectedProfiles :=
    match branch j with
    | .joint => degreeTwoTwelvePairJointProfiles (kappa j) (sectionCap j)
    | .core => degreeTwoTwelvePairExceptionalProfiles
    | .ternary => ∅
    | .paired => degreeTwoTwelvePairExceptionalProfiles
  expectedProfiles_eq := rfl

noncomputable def pairedSix : Fin 2 → DegreeTwoPairTopFiniteInterface 6 :=
  Fin.cases pairedSix1Interface <| Fin.cases pairedSix2Interface Fin.elim0

private def pairedPosition : Fin 2 → Fin 301 := ![194, 235]

private def pairedForward
    (j : {j : Fin 301 // (row j).branch = .paired}) : Fin 2 :=
  if j.1.val = 194 then 0 else 1

private def pairedBackward
    (i : Fin 2) : {j : Fin 301 // (row j).branch = .paired} :=
  ⟨pairedPosition i, by fin_cases i <;> native_decide⟩

private def pairedBinding :
    {j : Fin 301 // (row j).branch = .paired} ≃ Fin 2 where
  toFun := pairedForward
  invFun := pairedBackward
  left_inv := by native_decide +revert
  right_inv := by native_decide +revert

noncomputable def catalogue : DegreeTwoTwelvePairTopFiniteCatalogue where
  row := row
  pairedSix := pairedSix
  pairedSixBinding := pairedBinding
  joint_count := by native_decide
  core_count := by native_decide
  ternary_count := by native_decide
  paired_count := by native_decide

end DegreeTwoTwelvePairFiniteCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
