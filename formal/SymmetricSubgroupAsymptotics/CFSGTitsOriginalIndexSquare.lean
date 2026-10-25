import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleParabolicSolvable
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourAllParameterOrderLower
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The strict least-index square for the original Tits full-centre quotient.
The literal ambient parabolic is first restricted to the actual derived group,
then mapped through its full central quotient. Index only decreases in both
steps. Solubility proves its image proper under inherited nonabelian simplicity;
no containment of the full quotient kernel in the parabolic is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsOriginalIndexSquare
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourDerivedAmbientHom CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourMiddleParabolicFlag CFSGReeFFourMiddleGradedDerivedAction
open CFSGReeFFourBinaryMiddleParabolicSolvable CFSGReeFFourMiddleParabolicCardinality
open CFSGReeFFourBinaryOuterSaving CFSGReeFFourAllParameterOrderLower
open PrimitiveSocleRawStructure

private instance fixedFinite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

private instance titsFinite : Finite CFSG.Models.Tits :=
  Finite.of_surjective (derivedReeHom 0) (derivedReeHom_surjective 0)

private theorem restriction_index_le {G H : Type*} [Group G] [Group H] [Finite G]
    (P : Subgroup G) (f : H →* G) : (P.comap f).index ≤ P.index := by
  rw [Subgroup.index_comap]
  have hp : P.relIndex (⊤ : Subgroup G) ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact P.index_ne_zero_of_finite
  exact (Subgroup.relIndex_le_of_le_right (show f.range ≤ ⊤ from le_top) hp).trans_eq
    P.relIndex_top_right

private theorem image_index_le {G H : Type*} [Group G] [Group H] [Finite G]
    (P : Subgroup G) (f : G →* H) (hf : Function.Surjective f) :
    (P.map f).index ≤ P.index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero P.index_ne_zero_of_finite) (P.index_map_dvd hf)

theorem derivedParabolic_index_le : (derivedParabolic 0).index ≤ 1755 := by
  have hr : (derivedParabolic 0).index ≤ (middleParabolic 0).index :=
    restriction_index_le (middleParabolic 0) (commutator (originalModelFixed 0)).subtype
  have hp : (middleParabolic 0).index ≤ 1755 := by
    exact (middleParabolic_index_le 0).trans_eq (by decide)
  exact hr.trans hp

theorem originalParabolic_index_le : (originalParabolic 0).index ≤ 1755 :=
  (image_index_le (derivedParabolic 0) (derivedReeHom 0) (derivedReeHom_surjective 0)).trans
    derivedParabolic_index_le

theorem originalParabolic_ne_top [IsSimpleGroup CFSG.Models.Tits]
    (hn : ¬ IsMulCommutative CFSG.Models.Tits) : originalParabolic 0 ≠ ⊤ := by
  intro he
  letI : IsSolvable (originalParabolic 0) := originalParabolic_zero_solvable
  have hf : Function.Surjective (originalParabolic 0).subtype := by
    intro g
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [he]
    trivial
  have hs : IsSolvable CFSG.Models.Tits := solvable_of_surjective hf
  exact hn (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))

theorem order_lower : 4194304 ≤ Nat.card CFSG.Models.Tits := by
  calc
    _ = (2048 : ℕ)^2 := by decide
    _ ≤ (Nat.card (derivedPositive 0))^2 :=
      Nat.pow_le_pow_left derivedPositive_card_ge_2048 2
    _ ≤ _ := derivedPositive_square_le_original_order 0

theorem leastProperIndex_le [IsSimpleGroup CFSG.Models.Tits]
    (hn : ¬ IsMulCommutative CFSG.Models.Tits) (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Tits ell) : ell ≤ 1755 :=
  (hell.2 (originalParabolic 0) (originalParabolic_ne_top hn)).trans
    originalParabolic_index_le

theorem index_square [IsSimpleGroup CFSG.Models.Tits]
    (hn : ¬ IsMulCommutative CFSG.Models.Tits) (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Tits ell) : ell^2 < Nat.card CFSG.Models.Tits :=
  ((Nat.pow_le_pow_left (leastProperIndex_le hn ell hell) 2).trans_lt
    (by decide : (1755 : ℕ)^2 < 4194304)).trans_le order_lower

end SymmetricSubgroupAsymptotics.CFSGTitsOriginalIndexSquare
