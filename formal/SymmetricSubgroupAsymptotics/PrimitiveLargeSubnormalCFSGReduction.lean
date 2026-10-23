import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveAffineAllSubgroupsClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingSubnormalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalDClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleGTwoClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSuzukiClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalClassBound

/-! Exact remaining simple types for the large primitive SUBNORMAL
class-count target. All affine degrees and both raw socle degree forms
are retained. This is a reduction with an explicit surviving witness,
not a proof of the remaining exceptional or bounded-degree targets. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveLargeSubnormalCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction

def RemainingLargePrimitiveSimpleType : CFSG.Index → Prop
  | .cyclic _ _ | .alternating _ _ | .A _ _ _ _ | .B _ _ _ | .C _ _ _ _ | .D _ _ _
  | .twistedA _ _ _ _ | .twistedD _ _ _ | .G2 _ _ | .suzuki _ _ | .trialityD4 _
  | .E6 _ | .E7 _ | .E8 _ => False
  | _ => True

theorem primitive_subnormal_cube_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ K : Subgroup D.Simple,
        K≠⊤ ∧ Nat.card X=K.index^D.factorCount ∧
        ∃ i : CFSG.Index, RemainingLargePrimitiveSimpleType i ∧
          Nonempty (D.Simple ≃* i.Model) := by
  obtain ⟨P⟩ := publishedONanScottStructure G X
  cases P with
  | inr P =>
    exact Or.inl (PrimitiveAffineAllSubgroupsClassBound.subgroup_class_cube_le_garonziMaroti
      P inferInstance (Classical.choice inferInstance) (by omega) H)
  | inl D =>
    rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
    swap
    · exact Or.inl (D.subgroup_class_cube_le_of_power_form a hka hdegree hn H)
    let W := simpleModelWitness hCFSG D.Simple
    cases hi : W.index
    case cyclic p hp => exact (W.not_cyclic D.noncommutative p hp hi).elim
    case alternating m hm =>
      have e : D.Simple ≃* alternatingGroup (Fin m) := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subnormal_class_cube_le_of_alternating m hm e hn H hH)
    case A r q hr hs =>
      have e : D.Simple ≃* CFSG.Models.A r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_typeA r hr q e hn H)
    case C r q hr hs =>
      have e : D.Simple ≃* CFSG.Models.C r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_symplectic r hr q e hn H)
    case B r q hr =>
      have e : D.Simple ≃* CFSG.Models.B r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_orthogonalB r hr q e hn H)
    case D r q hr =>
      have e : D.Simple ≃* CFSG.Models.D r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_orthogonalD r hr q e hn H)
    case twistedA r q hr hs =>
      have e : D.Simple ≃* CFSG.Models.TwistedA r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_unitary r hr q hs e hn H)
    case twistedD r q hr =>
      have e : D.Simple ≃* CFSG.Models.TwistedD r q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_twistedD r hr q e hn H)
    case G2 q hs =>
      have e : D.Simple ≃* CFSG.Models.G2 q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_gTwo q hs e hn H)
    case suzuki m hm =>
      have e : D.Simple ≃* CFSG.Models.Suzuki m := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_suzuki m hm e hn H)
    case trialityD4 q =>
      have e : D.Simple ≃* CFSG.Models.TrialityD4 q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_triality q e hn H)
    case E6 q =>
      have e : D.Simple ≃* CFSG.Models.E6 q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_typeE6 q e hn H)
    case E7 q =>
      have e : D.Simple ≃* CFSG.Models.E7 q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_typeE7 q e hn H)
    case E8 q =>
      have e : D.Simple ≃* CFSG.Models.E8 q := by
        exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
      exact Or.inl (D.subgroup_class_cube_le_of_typeE8 q e hn H)
    all_goals
      exact Or.inr ⟨D,K,hK,hdegree,W.index,by simp [RemainingLargePrimitiveSimpleType,hi],
        ⟨W.equiv⟩⟩

end SymmetricSubgroupAsymptotics.PrimitiveLargeSubnormalCFSGReduction
