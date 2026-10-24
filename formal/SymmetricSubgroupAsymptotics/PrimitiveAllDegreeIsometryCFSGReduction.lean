import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeSharpClassicalCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBilinearClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryIsometryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneSharpClassCubeClassBound

/-! An exact all-degree refinement retaining the original raw socle,
model equivalence and degree witness. Every bounded classical residual
has explicit finite field/rank parameters, with actual pairing-isometry
order bounds for B/D/twisted-D/unitary and the sharp C recurrence; unhandled nonclassical types
and the existing large-degree residual remain literal. The original
subnormality premise is unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAllDegreeIsometryCFSGReduction
open PrimitiveSocleRawStructure CFSGReduction WeakClassicalOrderCubeNumerics
open PrimitiveAllDegreeSubnormalCFSGReduction PrimitiveLargeSubnormalCFSGReduction

def RemainingBoundedPrimitiveParameters : CFSG.Index → Prop
  | .cyclic _ _ | .alternating _ _ | .E6 _ | .E7 _ | .E8 _ => False
  | .A r q _ _ => (r=1 ∧ q.order≤16) ∨ (r=2 ∧ q.order≤6) ∨
      (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2)
  | .B r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-1)
  | .C r q _ _ => (r=2 ∧ q.order≤127) ∨ (3≤r ∧ SymplecticSharpOrderCubeNumerics.SmallParameters q.order (r-1))
  | .D r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-1)
  | .twistedA r q _ _ => (r=2 ∧ q.order≤7) ∨ (r=3 ∧ q.order≤3) ∨
      (4≤r ∧ r≤6 ∧ q.order=2)
  | .twistedD r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-2)
  | _ => True

theorem primitive_subnormal_cube_or_actual_remaining_parameters
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4≤Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧
        ((Nat.card X<1024 ∧ RemainingBoundedPrimitiveParameters i) ∨
          (1024≤Nat.card X ∧ RemainingLargePrimitiveSimpleType i)) ∧
        ((∃ K : Subgroup D.Simple, K≠⊤ ∧ Nat.card X=K.index^D.factorCount) ∨
          (∃ a : ℕ, D.factorCount≤2*a ∧ Nat.card X=(Nat.card D.Simple)^a)) := by
  rcases PrimitiveAllDegreeSubnormalCFSGReduction.primitive_subnormal_cube_or_actual_remaining_model
    hCFSG G X hn H hH with hc | ⟨D,i,⟨e⟩,hstate,hform⟩
  · exact Or.inl hc
  · rcases hstate with ⟨hsmall,hremaining⟩ | hlarge
    · cases i with
      | cyclic p hp =>
        exact (show False from hremaining).elim
      | alternating m hm =>
        exact (show False from hremaining).elim
      | E6 q =>
        exact (show False from hremaining).elim
      | E7 q =>
        exact (show False from hremaining).elim
      | E8 q =>
        exact (show False from hremaining).elim
      | A r q hr hs =>
        rcases D.subnormal_class_cube_or_typeA_sharp_class_finite_parameters r hr q e H hH with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .A r q hr hs, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | B r q hr =>
        rcases D.subgroup_class_cube_or_typeB_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .B r q hr, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | C r q hr hs =>
        rcases D.subgroup_class_cube_or_typeC_sharp_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .C r q hr hs, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | D r q hr =>
        rcases D.subgroup_class_cube_or_typeD_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .D r q hr, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | F4 q =>
        exact Or.inr ⟨D, .F4 q, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | G2 q hs =>
        exact Or.inr ⟨D, .G2 q hs, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | twistedA r q hr hs =>
        rcases D.subgroup_class_cube_or_unitary_isometry_small_parameters r hr q hs e H with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .twistedA r q hr hs, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | twistedD r q hr =>
        rcases D.subgroup_class_cube_or_typeTwistedD_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · exact Or.inr ⟨D, .twistedD r q hr, ⟨e⟩, Or.inl ⟨hsmall, hp⟩, hform⟩
      | twistedE6 q =>
        exact Or.inr ⟨D, .twistedE6 q, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | trialityD4 q =>
        exact Or.inr ⟨D, .trialityD4 q, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | suzuki m hm =>
        exact Or.inr ⟨D, .suzuki m hm, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | reeG2 m hm =>
        exact Or.inr ⟨D, .reeG2 m hm, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | reeF4 m hm =>
        exact Or.inr ⟨D, .reeF4 m hm, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | tits =>
        exact Or.inr ⟨D, .tits, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | sporadic t =>
        exact Or.inr ⟨D, .sporadic t, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
    · exact Or.inr ⟨D, i, ⟨e⟩, Or.inr hlarge, hform⟩

end SymmetricSubgroupAsymptotics.PrimitiveAllDegreeIsometryCFSGReduction
