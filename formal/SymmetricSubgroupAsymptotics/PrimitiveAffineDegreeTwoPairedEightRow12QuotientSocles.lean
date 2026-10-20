import SymmetricSubgroupAsymptotics.FiniteNormalStateSocleTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow12NormalStates

/-! One selected table instantiates the uniform quotient-socle theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow12QuotientSocles
open Non2UnipotentPrefixFiniteMenu
abbrev Source := PrimitiveAffineEightFrameRow21TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow21TopCertificate.group
abbrev Top := Subgroup.closure (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators)

noncomputable def normalRegistry : FiniteNormalStateRegistry Source :=
  FiniteNormalStateRegistry.ofWordRegistry
    PrimitiveAffineEightFrameRow21NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow21NormalCertificate.topAmbient PrimitiveAffineEightFrameRow21NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow21NormalCertificate.data PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.state_injective

private def leTest (i j : Fin 9) : Bool :=
  ((#[#[true, true, true, true, true, true, true, true, true], #[false, true, true, true, true, true, true, true, true], #[false, false, true, false, false, false, false, true, true], #[false, false, false, true, false, false, false, true, true], #[false, false, false, false, true, false, false, true, true], #[false, false, false, false, false, true, false, true, true], #[false, false, false, false, false, false, true, true, true], #[false, false, false, false, false, false, false, true, true], #[false, false, false, false, false, false, false, false, true]] : Array (Array Bool))[i.val]!)[j.val]!

private theorem leTest_checked : ∀ i j : Fin 9,
    leTest i j = true ↔ PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.MaskLE i j := by decide +kernel

private def carrier (i : Fin 9) : Fin 9 :=
  (#[1, 7, 7, 7, 7, 7, 7, 8, 8] : Array (Fin 9))[i.val]!

private def generator (i : Fin 9) (j : Fin 2) : Source :=
  ⟨((#[#[0, 7], #[1, 5], #[0, 5], #[0, 1], #[0, 1], #[0, 1], #[0, 1], #[0, 4], #[0, 0]] : Array (Array (Fin 96)))[i.val]!)[j.val]!⟩

private def generatorIn (i k : Fin 9) : Bool :=
  ((#[#[false, true, true, true, true, true, true, true, true], #[false, false, false, false, false, false, false, true, true], #[false, false, false, true, false, false, false, true, true], #[false, false, true, false, false, false, false, true, true], #[false, false, true, false, false, false, false, true, true], #[false, false, true, false, false, false, false, true, true], #[false, false, true, false, false, false, false, true, true], #[false, false, false, false, false, false, false, false, true], #[true, true, true, true, true, true, true, true, true]] : Array (Array Bool))[i.val]!)[k.val]!

private theorem generatorIn_checked : ∀ i k : Fin 9,
    generatorIn i k = true ↔ ∀ j : Fin 2,
      PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask k (generator i j).index = true := by decide +kernel

private theorem carrier_upper_checked : ∀ i : Fin 9,
    leTest i (carrier i) = true ∧ ∀ j : Fin 9,
      finiteNormalTableMinimal leTest i j → leTest j (carrier i) = true := by decide +kernel

private theorem carrier_least_checked : ∀ i k : Fin 9, leTest i k = true →
    (∀ j : Fin 9, finiteNormalTableMinimal leTest i j → leTest j k = true) →
      leTest (carrier i) k = true := by decide +kernel

private theorem generator_mem_checked : ∀ i : Fin 9,
    generatorIn i (carrier i) = true := by decide +kernel

private theorem generator_generates_checked : ∀ i k : Fin 9,
    leTest i k = true → generatorIn i k = true → leTest (carrier i) k = true := by decide +kernel

noncomputable def socleTable : FiniteNormalStateSocleTable normalRegistry 2 where
  leTest := leTest
  le_iff i j := (PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.state_le_iff_maskLE i j).trans (leTest_checked i j).symm
  carrier := carrier
  carrier_upper := carrier_upper_checked
  carrier_least := carrier_least_checked
  generator := generator
  generatorIn := generatorIn
  generatorIn_iff i k := (generatorIn_checked i k).trans
    (forall_congr' (fun j ↦ PrimitiveAffineDegreeTwoPairedEightRow12NormalStates.normalMask_mem k (generator i j)))
  generator_mem := generator_mem_checked
  generator_generates := generator_generates_checked

/-- All literal normal axes are discharged by the same checked table. -/
theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.dispatch
    (normalRegistry.mapEquiv PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv)
    (socleTable.mapFamily PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv) N

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow12QuotientSocles
end
