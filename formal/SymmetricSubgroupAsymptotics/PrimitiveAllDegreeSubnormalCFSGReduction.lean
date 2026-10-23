import SymmetricSubgroupAsymptotics.PrimitiveLargeSubnormalCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingAllDegreesClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalAllDegreesClassBound

/-! Exact all-degree primitive reduction, for the GM target n>=4.
The alternating type and E6/E7/E8 are removed at every degree. All other
bounded cases retain the original raw socle, an actual CFSG isomorphism,
and the literal subgroup-index or group-power degree witness. Large
cases retain the existing smaller residual type predicate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeSubnormalCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveSimpleType : CFSG.Index → Prop
  | .cyclic _ _ | .alternating _ _ | .E6 _ | .E7 _ | .E8 _ => False
  | _ => True

theorem primitive_subnormal_cube_or_actual_remaining_model
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X < 1024 ∧ RemainingBoundedPrimitiveSimpleType i) ∨
          (1024 ≤ Nat.card X ∧ RemainingLargePrimitiveSimpleType i)) ∧
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2 * a ∧ Nat.card X = (Nat.card D.Simple) ^ a)) := by
  by_cases hlarge : 1024 ≤ Nat.card X
  · rcases PrimitiveLargeSubnormalCFSGReduction.primitive_subnormal_cube_or_actual_remaining_model
        hCFSG G X hlarge H hH with hc | ⟨D, K, hK, hdegree, i, hi, he⟩
    · exact Or.inl hc
    · exact Or.inr ⟨D, i, he, Or.inr ⟨hlarge, hi⟩, Or.inl ⟨K, hK, hdegree⟩⟩
  · have hsmall : Nat.card X < 1024 := by omega
    obtain ⟨P⟩ := publishedONanScottStructure G X
    cases P with
    | inr P =>
      exact Or.inl (PrimitiveAffineAllSubgroupsClassBound.subgroup_class_cube_le_garonziMaroti
        P inferInstance (Classical.choice inferInstance) hn H)
    | inl D =>
      let W := simpleModelWitness hCFSG D.Simple
      cases hi : W.index with
      | cyclic p hp => exact (W.not_cyclic D.noncommutative p hp hi).elim
      | alternating m hm =>
        have e : D.Simple ≃* alternatingGroup (Fin m) := by
          exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
        exact Or.inl (D.subnormal_class_cube_le_of_alternating_all_degrees m hm e H hH)
      | E6 q =>
        have e : D.Simple ≃* CFSG.Models.E6 q := by
          exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
        exact Or.inl (D.subgroup_class_cube_le_of_typeE6_allDegrees q e H)
      | E7 q =>
        have e : D.Simple ≃* CFSG.Models.E7 q := by
          exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
        exact Or.inl (D.subgroup_class_cube_le_of_typeE7_allDegrees q e H)
      | E8 q =>
        have e : D.Simple ≃* CFSG.Models.E8 q := by
          exact Eq.mp (congrArg (fun j : CFSG.Index => D.Simple ≃* j.Model) hi) W.equiv
        exact Or.inl (D.subgroup_class_cube_le_of_typeE8_allDegrees q e H)
      | A r q hr hs =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | B r q hr =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | C r q hr hs =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | D r q hr =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | F4 q =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | G2 q hs =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | twistedA r q hr hs =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | twistedD r q hr =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | twistedE6 q =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | trialityD4 q =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | suzuki m hm =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | reeG2 m hm =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | reeF4 m hm =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | tits =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩
      | sporadic t =>
        exact Or.inr ⟨D, W.index, ⟨W.equiv⟩,
          Or.inl ⟨hsmall, by simp [RemainingBoundedPrimitiveSimpleType, hi]⟩, D.indexForm⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeSubnormalCFSGReduction
