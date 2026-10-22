import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! The literal positive Sylow has centre of field cardinality in each
ORIGINAL simple E6/E7/E8 projective Serre model. The checked exceptional
sign and normalizer-word identities discharge every generic premise.
No assertion about arbitrary model automorphisms is made here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalSylowCenters
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGSignedCartanReflections CFSGExceptionalNormalizerWordIdentity
open CFSGNormTwoCoordinateOriginalPositiveSylow CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem exists_sylow_center_card_of_coordinate_cartan_eq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (CFSGIntegerMatrixPairing.rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),
      CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w∈
      Subgroup.normalizer (CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K false : Set _)→
      CFSGNormTwoGeckWeylLatticeLinear.wordLinear A hs hp
        (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w=1)
    {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : CFSGGeckSerreRepresentation.cartan
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)=C)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)] :
    ∃P : Sylow p (Projective C K),Nat.card (Subgroup.center P)=Nat.card K := by
  subst C
  let i : Fin r := Classical.arbitrary (Fin r)
  exact ⟨originalPositiveSylow A hd hs hp ho K ε hε hA hidentity p i,
    original_positive_sylow_center_card A hd hs hp ho K ε hε hA hidentity p i⟩

theorem serreTypeE6_exists_sylow_center_card (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    ∃P : Sylow p (Projective CartanMatrix.E₆ K),Nat.card (Subgroup.center P)=Nat.card K := by
  have hC := E6_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)=CartanMatrix.E₆ at hC
  exact exists_sylow_center_card_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) hC p

theorem serreTypeE7_exists_sylow_center_card (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    ∃P : Sylow p (Projective CartanMatrix.E₇ K),Nat.card (Subgroup.center P)=Nat.card K := by
  have hC := E7_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)=CartanMatrix.E₇ at hC
  exact exists_sylow_center_card_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    K E7Signs E7_signs_square E7_signs_cartan (E7_normalizer_word_identity K) hC p

theorem serreTypeE8_exists_sylow_center_card (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    ∃P : Sylow p (Projective CartanMatrix.E₈ K),Nat.card (Subgroup.center P)=Nat.card K := by
  have hC := E8_cartan
  change CFSGGeckSerreRepresentation.cartan
    (coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)=CartanMatrix.E₈ at hC
  exact exists_sylow_center_card_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos
    K E8Signs E8_signs_square E8_signs_cartan (E8_normalizer_word_identity K) hC p

theorem typeE6_exists_sylow_center_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    ∃P : Sylow q.prime (CFSG.Models.E6 q),Nat.card (Subgroup.center P)=q.order := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE6_exists_sylow_center_card q.Field q.prime

theorem typeE7_exists_sylow_center_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    ∃P : Sylow q.prime (CFSG.Models.E7 q),Nat.card (Subgroup.center P)=q.order := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE7_exists_sylow_center_card q.Field q.prime

theorem typeE8_exists_sylow_center_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    ∃P : Sylow q.prime (CFSG.Models.E8 q),Nat.card (Subgroup.center P)=q.order := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE8_exists_sylow_center_card q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalSylowCenters
