import SymmetricSubgroupAsymptotics.ScalarFourCentralRawSummedCount
import SymmetricSubgroupAsymptotics.ScalarFourCentralC4RawSummedCount
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-! Structural choices on each SAME original normal quotient. A character
certificate is an actual jointly faithful tuple; central choices are actual
nonsplit kernel/active coordinate maps. This is not a normal-list locator
or a numerical source-capacity assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu

structure BinaryCentral (Q : Type) [Group Q] : Type 1 where
  T : Type
  [groupT : Group T]
  [finiteT : Finite T]
  c : ℕ
  d : ℕ
  coordinates : ScalarFourCentralTopCoordinates Q T c d
  central_rank : c≤3
  active_rank : d≤3
  topEmbedding : T →* Equiv.Perm (Fin 3)
  topEmbedding_injective : Function.Injective topEmbedding

structure CyclicFourCentral (Q : Type) [Group Q] : Type 1 where
  T : Type
  [groupT : Group T]
  [finiteT : Finite T]
  c : ℕ
  d : ℕ
  coordinates : ScalarFourCentralC4TopCoordinates Q T c d
  central_rank : c≤3
  active_rank : d≤3
  topEmbedding : T →* Equiv.Perm (Fin 3)
  topEmbedding_injective : Function.Injective topEmbedding

attribute [instance] BinaryCentral.groupT BinaryCentral.finiteT
  CyclicFourCentral.groupT CyclicFourCentral.finiteT

/-- A genuine structural witness for one quotient, before any source J is seen. -/
def Choice (Q : Type) [Group Q] : Prop :=
  (∃ C : CharacterQuotientCertificate Q, C.slope≤(381/192 : ℝ)) ∨
    Nonempty (BinaryCentral Q) ∨ Nonempty (CyclicFourCentral Q)

end SymmetricSubgroupAsymptotics.OriginalNormalAxisSourceMenu
