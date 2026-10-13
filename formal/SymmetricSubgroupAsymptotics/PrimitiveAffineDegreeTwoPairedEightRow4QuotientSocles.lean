import SymmetricSubgroupAsymptotics.FiniteNormalStateSocleTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4NormalStates

/-! One selected table instantiates the uniform quotient-socle theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4QuotientSocles
open Non2UnipotentPrefixFiniteMenu
abbrev Source := PrimitiveAffineEightFrameRow3TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow3TopCertificate.group
abbrev Top := Subgroup.closure (Set.range PrimitiveAffineEightFrameRow3TopCertificate.generators)

noncomputable def normalRegistry : FiniteNormalStateRegistry Source :=
  FiniteNormalStateRegistry.ofWordRegistry
    PrimitiveAffineEightFrameRow3NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameRow3NormalCertificate.topAmbient PrimitiveAffineEightFrameRow3NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameRow3NormalCertificate.data PrimitiveAffineDegreeTwoPairedEightRow4NormalStates.state_injective

private def leTest (i j : Fin 7) : Bool :=
  ((#[#[true, true, true, true, true, true, true], #[false, true, false, false, true, true, true], #[false, false, true, false, true, true, true], #[false, false, false, true, true, true, true], #[false, false, false, false, true, true, true], #[false, false, false, false, false, true, true], #[false, false, false, false, false, false, true]] : Array (Array Bool))[i.val]!)[j.val]!

private theorem leTest_checked : ∀ i j : Fin 7,
    leTest i j = true ↔ PrimitiveAffineDegreeTwoPairedEightRow4NormalStates.MaskLE i j := by decide +kernel

private def carrier (i : Fin 7) : Fin 7 :=
  (#[4, 4, 4, 4, 5, 6, 6] : Array (Fin 7))[i.val]!

private def generator (i : Fin 7) (j : Fin 2) : Source :=
  ⟨((#[#[0, 2], #[0, 2], #[0, 2], #[0, 2], #[0, 1], #[0, 6], #[0, 0]] : Array (Array (Fin 96)))[i.val]!)[j.val]!⟩

private def generatorIn (i k : Fin 7) : Bool :=
  ((#[#[false, false, false, false, true, true, true], #[false, false, false, false, true, true, true], #[false, false, false, false, true, true, true], #[false, false, false, false, true, true, true], #[false, false, false, false, false, true, true], #[false, false, false, false, false, false, true], #[true, true, true, true, true, true, true]] : Array (Array Bool))[i.val]!)[k.val]!

private theorem generatorIn_checked : ∀ i k : Fin 7,
    generatorIn i k = true ↔ ∀ j : Fin 2,
      PrimitiveAffineDegreeTwoPairedEightRow4NormalStates.normalMask k (generator i j).index = true := by decide +kernel

private theorem carrier_upper_checked : ∀ i : Fin 7,
    leTest i (carrier i) = true ∧ ∀ j : Fin 7,
      finiteNormalTableMinimal leTest i j → leTest j (carrier i) = true := by decide +kernel

private theorem carrier_least_checked : ∀ i k : Fin 7, leTest i k = true →
    (∀ j : Fin 7, finiteNormalTableMinimal leTest i j → leTest j k = true) →
      leTest (carrier i) k = true := by decide +kernel

private theorem generator_mem_checked : ∀ i : Fin 7,
    generatorIn i (carrier i) = true := by decide +kernel

private theorem generator_generates_checked : ∀ i k : Fin 7,
    leTest i k = true → generatorIn i k = true → leTest (carrier i) k = true := by decide +kernel

noncomputable def socleTable : FiniteNormalStateSocleTable normalRegistry 2 where
  leTest := leTest
  le_iff i j := (PrimitiveAffineDegreeTwoPairedEightRow4NormalStates.state_le_iff_maskLE i j).trans (leTest_checked i j).symm
  carrier := carrier
  carrier_upper := carrier_upper_checked
  carrier_least := carrier_least_checked
  generator := generator
  generatorIn := generatorIn
  generatorIn_iff i k := (generatorIn_checked i k).trans
    (forall_congr' (fun j ↦ PrimitiveAffineDegreeTwoPairedEightRow4NormalStates.normalMask_mem k (generator i j)))
  generator_mem := generator_mem_checked
  generator_generates := generator_generates_checked

/-- All literal normal axes are discharged by the same checked table. -/
theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.dispatch
    (normalRegistry.mapEquiv PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv)
    (socleTable.mapFamily PrimitiveAffineEightFrameRow3TopCertificate.originalEquiv) N

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow4QuotientSocles
end
