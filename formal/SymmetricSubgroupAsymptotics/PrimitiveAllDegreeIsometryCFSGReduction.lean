import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeSharpClassicalCFSGReduction
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBilinearClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleUnitaryIsometryOrderCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneCompleteClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankTwoCompleteClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAClassEquationCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeASmallOrderClassEquation
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeABinaryCyclicClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOddRankTwoClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticOddHigherRankClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryHigherRankClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalDPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDPointRadicalClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticSmallOddPrimeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSymplecticBinaryRankTwoClassBound
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

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
  | .A _ _ _ _ => False
  | .B r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-1) ∧
      ¬ClassicalClassEquationCapacity.typeB r q ∧
      q.prime=2 ∧ ¬(4≤q.order ∨ 5≤r)
  | .C r q _ _ => (r=2 ∧ q.order≤7 ∧ q.prime=2) ∨
      (3≤r ∧ SymplecticSharpOrderCubeNumerics.SmallParameters q.order (r-1) ∧
        q.prime=2 ∧ ¬(4≤q.order ∨ 5≤r))
  | .D r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-1) ∧
      ¬ClassicalClassEquationCapacity.typeD r q ∧ ¬(3≤q.order ∨ 5≤r)
  | .twistedA r q _ _ => ((r=2 ∧ q.order≤7) ∨ (r=3 ∧ q.order≤3) ∨
      (4≤r ∧ r≤6 ∧ q.order=2)) ∧ ¬ClassicalClassEquationCapacity.unitary r q
  | .twistedD r q _ => OrthogonalBilinearOrderCubeNumerics.SmallParameters q.order (r-2) ∧
      ¬ClassicalClassEquationCapacity.twistedD r q ∧ ¬(3≤q.order ∨ 5≤r)
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
        by_cases htwo:r=2
        · subst r
          exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_two_all_fields q e H hH)
        · rcases D.subnormal_class_cube_or_typeA_higher_rank_parameters r hr q hs e H hH with hc | hp
          · exact Or.inl hc
          · rcases hp with ⟨h2,_⟩ | hp
            · exact (htwo h2).elim
            · by_cases hsix : r=6
              · subst r
                exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_six_card_two q
                  (by omega) e H hH)
              · by_cases hthree : r=3 ∧ q.order=3
                · rcases hthree with ⟨rfl, hq⟩
                  exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_three_card_three q hq e H hH)
                · by_cases hfour : r=4
                  · subst r
                    exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_four_card_two q
                      (by omega) e H hH)
                  · have hqlo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
                      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
                    exact Or.inl (D.subnormal_class_cube_le_of_typeA_binary_cyclic r
                      (by omega) q (by omega) e H hH)
      | B r q hr =>
        rcases D.subgroup_class_cube_or_typeB_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · by_cases hb : ClassicalClassEquationCapacity.typeB r q
          · exact Or.inl (D.subnormal_class_cube_le_of_typeB_class_equation r hr q e hb H hH)
          · by_cases hbinary : q.prime=2
            · by_cases hwindow : 4≤q.order ∨ 5≤r
              · exact Or.inl (D.subgroup_class_cube_le_of_typeB_binary_higher_rank
                  r hr q hbinary e hwindow H)
              · exact Or.inr ⟨D, .B r q hr, ⟨e⟩,
                  Or.inl ⟨hsmall, hp, hb, hbinary, hwindow⟩, hform⟩
            · exact Or.inl (D.subgroup_class_cube_le_of_typeB_point_radical
                r hr q hbinary e H)
      | C r q hr hs =>
        rcases D.subgroup_class_cube_or_typeC_sharp_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · rcases hp with ⟨rfl, hq⟩ | hp
          · by_cases hbinary : q.prime=2
            · by_cases hlarge : 8 ≤ q.order
              · exact Or.inl (D.subgroup_class_cube_le_of_typeC_binary_rank_two q hlarge hbinary e H)
              · exact Or.inr ⟨D, .C 2 q hr hs, ⟨e⟩,
                  Or.inl ⟨hsmall, Or.inl ⟨rfl, by omega, hbinary⟩⟩, hform⟩
            · exact Or.inl (D.subnormal_class_cube_le_of_typeC_odd_rank_two_all_fields q hbinary e H hH)
          · by_cases hbinary : q.prime=2
            · by_cases hwindow : 4≤q.order ∨ 5≤r
              · exact Or.inl (D.subgroup_class_cube_le_of_typeC_binary_higher_rank
                  r hp.1 q hbinary e hwindow H)
              · exact Or.inr ⟨D, .C r q hr hs, ⟨e⟩,
                  Or.inl ⟨hsmall, Or.inr ⟨hp.1, hp.2, hbinary, hwindow⟩⟩, hform⟩
            · exact Or.inl (D.subgroup_class_cube_le_of_typeC_odd_higher_rank r hp.1 q hbinary e H)
      | D r q hr =>
        rcases D.subgroup_class_cube_or_typeD_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · by_cases hb : ClassicalClassEquationCapacity.typeD r q
          · exact Or.inl (D.subnormal_class_cube_le_of_typeD_class_equation r hr q e hb H hH)
          · by_cases hwindow : 3≤q.order ∨ 5≤r
            · exact Or.inl (D.subgroup_class_cube_le_of_typeD_point_radical r hr q e hwindow H)
            · exact Or.inr ⟨D, .D r q hr, ⟨e⟩, Or.inl ⟨hsmall, hp, hb, hwindow⟩, hform⟩
      | F4 q =>
        exact Or.inr ⟨D, .F4 q, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | G2 q hs =>
        exact Or.inr ⟨D, .G2 q hs, ⟨e⟩,
          Or.inl ⟨hsmall, trivial⟩, hform⟩
      | twistedA r q hr hs =>
        rcases D.subgroup_class_cube_or_unitary_isometry_small_parameters r hr q hs e H with hc | hp
        · exact Or.inl hc
        · by_cases hb : ClassicalClassEquationCapacity.unitary r q
          · exact Or.inl (D.subnormal_class_cube_le_of_unitary_class_equation r hr q hs e hb H hH)
          · exact Or.inr ⟨D, .twistedA r q hr hs, ⟨e⟩, Or.inl ⟨hsmall, hp, hb⟩, hform⟩
      | twistedD r q hr =>
        rcases D.subgroup_class_cube_or_typeTwistedD_bilinear_finite_parameters r hr q e H with hc | hp
        · exact Or.inl hc
        · by_cases hb : ClassicalClassEquationCapacity.twistedD r q
          · exact Or.inl (D.subnormal_class_cube_le_of_twistedD_class_equation r hr q e hb H hH)
          · by_cases hwindow : 3≤q.order ∨ 5≤r
            · exact Or.inl (D.subgroup_class_cube_le_of_twistedD_point_radical r hr q e hwindow H)
            · exact Or.inr ⟨D, .twistedD r q hr, ⟨e⟩,
                Or.inl ⟨hsmall, hp, hb, hwindow⟩, hform⟩
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
