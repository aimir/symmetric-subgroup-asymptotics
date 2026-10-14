import SymmetricSubgroupAsymptotics.FiniteNormalStateSocleTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow16NormalStates

/-! One selected table instantiates the uniform quotient-socle theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow16QuotientSocles
open Non2UnipotentPrefixFiniteMenu
abbrev Source := PrimitiveAffineEightFrameTop16TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameTop16TopCertificate.group
abbrev Top := Subgroup.closure (Set.range PrimitiveAffineEightFrameTop16TopCertificate.generators)

noncomputable def normalRegistry : FiniteNormalStateRegistry Source :=
  FiniteNormalStateRegistry.ofWordRegistry
    PrimitiveAffineEightFrameTop16NormalCertificate.topConjugacy.toCardinalCover
    PrimitiveAffineEightFrameTop16NormalCertificate.topAmbient PrimitiveAffineEightFrameTop16NormalCertificate.stateGenerators
    PrimitiveAffineEightFrameTop16NormalCertificate.data PrimitiveAffineDegreeTwoPairedEightRow16NormalStates.state_injective

private def leTest (i j : Fin 8) : Bool :=
  ((#[#[true, true, true, true, true, true, true, true], #[false, true, true, true, true, true, true, true], #[false, false, true, false, false, true, true, true], #[false, false, false, true, false, true, true, true], #[false, false, false, false, true, true, true, true], #[false, false, false, false, false, true, true, true], #[false, false, false, false, false, false, true, true], #[false, false, false, false, false, false, false, true]] : Array (Array Bool))[i.val]!)[j.val]!

private theorem leTest_checked : ∀ i j : Fin 8,
    leTest i j = true ↔ PrimitiveAffineDegreeTwoPairedEightRow16NormalStates.MaskLE i j := by decide +kernel

private def carrier (i : Fin 8) : Fin 8 :=
  (#[1, 5, 5, 5, 5, 6, 7, 7] : Array (Fin 8))[i.val]!

private def generator (i : Fin 8) (j : Fin 2) : Source :=
  ⟨((#[#[0, 7], #[0, 32], #[0, 16], #[0, 1], #[0, 1], #[0, 19], #[0, 4], #[0, 0]] : Array (Array (Fin 192)))[i.val]!)[j.val]!⟩

private def generatorIn (i k : Fin 8) : Bool :=
  ((#[#[false, true, true, true, true, true, true, true], #[false, false, false, false, false, true, true, true], #[false, false, false, false, true, true, true, true], #[false, false, true, false, false, true, true, true], #[false, false, true, false, false, true, true, true], #[false, false, false, false, false, false, true, true], #[false, false, false, false, false, false, false, true], #[true, true, true, true, true, true, true, true]] : Array (Array Bool))[i.val]!)[k.val]!

private theorem generatorIn_checked : ∀ i k : Fin 8,
    generatorIn i k = true ↔ ∀ j : Fin 2,
      PrimitiveAffineDegreeTwoPairedEightRow16NormalStates.normalMask k (generator i j).index = true := by decide +kernel

private theorem carrier_upper_checked : ∀ i : Fin 8,
    leTest i (carrier i) = true ∧ ∀ j : Fin 8,
      finiteNormalTableMinimal leTest i j → leTest j (carrier i) = true := by decide +kernel

private theorem carrier_least_checked : ∀ i k : Fin 8, leTest i k = true →
    (∀ j : Fin 8, finiteNormalTableMinimal leTest i j → leTest j k = true) →
      leTest (carrier i) k = true := by decide +kernel

private theorem generator_mem_checked : ∀ i : Fin 8,
    generatorIn i (carrier i) = true := by decide +kernel

private theorem generator_generates_checked : ∀ i k : Fin 8,
    leTest i k = true → generatorIn i k = true → leTest (carrier i) k = true := by decide +kernel

noncomputable def socleTable : FiniteNormalStateSocleTable normalRegistry 2 where
  leTest := leTest
  le_iff i j := (PrimitiveAffineDegreeTwoPairedEightRow16NormalStates.state_le_iff_maskLE i j).trans (leTest_checked i j).symm
  carrier := carrier
  carrier_upper := carrier_upper_checked
  carrier_least := carrier_least_checked
  generator := generator
  generatorIn := generatorIn
  generatorIn_iff i k := (generatorIn_checked i k).trans
    (forall_congr' (fun j ↦ PrimitiveAffineDegreeTwoPairedEightRow16NormalStates.normalMask_mem k (generator i j)))
  generator_mem := generator_mem_checked
  generator_generates := generator_generates_checked

/-- All literal normal axes are discharged by the same checked table. -/
theorem topSocle (N : {N : Subgroup Top // N.Normal}) :
    SocleNormalGeneratorBound (Top ⧸ N.1) 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.dispatch
    (normalRegistry.mapEquiv PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv)
    (socleTable.mapFamily PrimitiveAffineEightFrameTop16TopCertificate.originalEquiv) N

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow16QuotientSocles
end
