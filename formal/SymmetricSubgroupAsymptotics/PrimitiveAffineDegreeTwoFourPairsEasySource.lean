import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveRecoveredNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7AbstractS4Source
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailInstance
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSelfEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSmallAdditiveRawEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoY1RawEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage

/-!
# Already-integrated rows in the four-pair slice

Three of the ten width-eight pair actions already have complete source
constructors: the two linear actions, either degree-eight representation of
the abstract group `S4`, and the repeated-natural-`A4` (`Y1`) row.  This
file is only their source dispatcher.  It makes no assertion that an
arbitrary four-pair action lies in this list.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

inductive CertifiedFourPairEasyModel
    (U : PreE7NonPairActionClass 8) : Type 1
  | linear (source : PreE7LinSource 8 U)
  | abstractSymmetricFour
      (equiv : preE7NonPairAction 8 U ≃* Equiv.Perm (Fin 4))
  | repeatedNaturalA4 (source : PreE7Y1SourceData 8 U)

namespace CertifiedFourPairEasyModel

open Equiv

/-- The abstract `S4` complete-source theorem does not depend on which
faithful degree-eight representation supplied the four-pair row. -/
def abstractS4Model
    {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* Perm (Fin 4)) :
    PreE7NormalComparatorModel 8 U where
  G := Perm (Fin 4)
  equiv := e
  index := Unit
  R := Perm (Fin 3)
  degree := 3
  action := MonoidHom.id _
  action_injective := Function.injective_id
  proj := fun _ => NaturalS4.pairing
  proj_surjective := fun _ => NaturalS4.pairing_surjective
  normal_cover := fun N hN hNb => by
    haveI := hN
    refine ⟨(), ?_⟩
    rw [NaturalS4.ker_pairing]
    exact le_of_minimal_selfCentralizing NaturalS4.klein
      NaturalS4.klein_minimal NaturalS4.klein_selfCentralizing N hNb
  tailSlope := 1 / 4
  tailConstant := 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4))
  tailConstant_nonneg := by positivity
  tail := fun _ J => NaturalS4.epi_card_le J
  comparator_window := by
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := by
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]

private theorem abstractS4_aut_tail_le :
    (2 : ℝ) * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤
      (2 : ℝ) ^ (144 : ℝ) := by
  let G := Perm (Fin 4)
  have h : Nat.card (G ≃* G) ≤ 24 ^ 24 := by
    have hraw := mulEquiv_card_le_card_pow_card G
    calc
      Nat.card (G ≃* G) ≤ Nat.card G ^ Nat.card G := hraw
      _ = 24 ^ 24 := by
        congr 1 <;> rw [Nat.card_perm, Nat.card_fin] <;> norm_num
  have hnat : 2 * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤ 2 ^ 144 :=
    (Nat.mul_le_mul_left 2 h).trans (by norm_num)
  exact_mod_cast hnat

/-- Complete width-eight numerical package for the nonnatural `S4` row. -/
noncomputable def abstractS4NumericalData
    {U : PreE7NonPairActionClass 8}
    (e : preE7NonPairAction 8 U ≃* Perm (Fin 4)) :
    PreE7SmallAdditiveNumericalData .s4 8 U := by
  let M := abstractS4Model e
  apply M.numericalData .s4
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction 8 U) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) :=
        M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (24 : ℝ) := by
        have hcard : Nat.card M.G = 24 := by
          change Nat.card (Perm (Fin 4)) = 24
          rw [Nat.card_perm, Nat.card_fin]
          norm_num
        congr 1
        exact_mod_cast hcard
      _ ≤ (2 : ℝ) ^ (16 * (8 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (w := 8) (by norm_num) b
  · intro b
    change (2 : ℝ) * Nat.card (Perm (Fin 4) ≃* Perm (Fin 4)) ≤ _
    calc
      _ ≤ (2 : ℝ) ^ (144 : ℝ) := abstractS4_aut_tail_le
      _ ≤ (2 : ℝ) ^ (36 * (8 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        norm_num
      _ ≤ _ := two_rpow_thirtySix_width_le_menuMass (w := 8) (by norm_num) b

/-- The compressed literal complete-quotient envelope underlying each easy
owner.  LIN and `S4` use their small comparator; Y1 retains its cold/hot
rank-tail split. -/
noncomputable def quotientSummedEnvelope
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U) :
    PreE7DegreeTwoPairQuotientSummedEnvelope (preE7NonPairAction 8 U) :=
  match M with
  | .linear (.gl e h) => (linGLModel U e h).toData.quotientSummedEnvelope
  | .linear (.sl e h) => (linSLModel U e h).toData.quotientSummedEnvelope
  | .abstractSymmetricFour e =>
      (abstractS4Model e).toData.quotientSummedEnvelope
  | .repeatedNaturalA4 S => S.quotientSummedEnvelope lit

/-- The compressed raw row together with its actual faithful comparator
action.  In the Y1 rank-tail row the comparator is trivial, so its faithful
action is padded to two fixed points for the common growing-comparator
interface. -/
noncomputable def quotientSummedPackage
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 8 U) := by
  cases M with
  | linear S =>
      cases S with
      | gl e h =>
          let D := (linGLModel U e h).toData
          exact
            { envelope := D.quotientSummedEnvelope
              v := D.degree
              action := D.action
              action_injective := D.action_injective }
      | sl e h =>
          let D := (linSLModel U e h).toData
          exact
            { envelope := D.quotientSummedEnvelope
              v := D.degree
              action := D.action
              action_injective := D.action_injective }
  | abstractSymmetricFour e =>
      let D := (abstractS4Model e).toData
      exact
        { envelope := D.quotientSummedEnvelope
          v := D.degree
          action := D.action
          action_injective := D.action_injective }
  | repeatedNaturalA4 S =>
      exact
        { envelope := S.quotientSummedEnvelope lit
          v := 2
          action := (1 : PUnit →* Equiv.Perm (Fin 2))
          action_injective := by
            change Function.Injective (1 : PUnit →* Equiv.Perm (Fin 2))
            intro x y _
            exact Subsingleton.elim x y }

/-- Dispatch only to owner constructors whose numerical packages are
already checked independently of the four-pair classification. -/
noncomputable def source
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U) :
    PreE7RankTailSourceOrYonedaTopData 8 U :=
  match M with
  | .linear S =>
      .inl (.ordinary .lin (.small (preE7_lin_numericalData 8 U S)))
  | .abstractSymmetricFour e =>
      .inl (.ordinary .s4 (.small (abstractS4NumericalData e)))
  | .repeatedNaturalA4 S => .inl (.y1 S)

end CertifiedFourPairEasyModel
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
