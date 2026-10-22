import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData
import SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtomCount

/-! An actual field-sized root subgroup with an automorphism-invariant
conjugacy family in each ORIGINAL simple E6/E7/E8 model. The witness is
constructed from the SAME projected dominant root and literal positive
Sylow, with every exceptional sign and normalizer-word premise proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalIntrinsicRootFamily
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGSignedCartanReflections CFSGExceptionalNormalizerWordIdentity
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateOriginalPositiveCenter CFSGNormTwoCoordinateOriginalPositiveCenterCardinality
open CFSGNormTwoCoordinatePositiveCenter CFSGNormTwoCoordinateOriginalRootFamily
open CFSGNormalizerCenterAtoms
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem exists_root_family_of_coordinate_cartan_eq {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef) (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K : Type) [Field K] [Finite K]
    (ε : Fin r→ℤ) (hε : ∀j,ε j*ε j=1) (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (hidentity : ∀w : List (Fin r),wordUnit A hs hp
      (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) K w∈
      Subgroup.normalizer (rootGroup A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho) K false : Set _)→
      wordLinear A hs hp (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho) w=1)
    {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)=C)
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)] :
    ∃L : Subgroup (Projective C K),Nat.card L=Nat.card K ∧
      ∀ (f : MulAut (Projective C K)) (g : Projective C K),
        ∃h : Projective C K,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  subst C
  let i : Fin r := Classical.arbitrary _
  obtain ⟨θ,hθ,hdom,_⟩ := exists_root_subgroup_center A hd hs hp ho K
  let L := originalRootLine A hd hs hp ho K i θ
  have hL : centerImage (originalPositive A hd hs hp ho K i)=L :=
    original_positive_center_eq_dominant_image A hd hs hp ho K p i θ hθ hdom
  refine ⟨L,?_,?_⟩
  · rw [←hL,centerImage_card]
    exact original_positive_center_card A hd hs hp ho K p i
  · intro f g
    exact automorphism_maps_originalConjugateRootLine A hd hs hp ho K
      ε hε hA hidentity p i θ hθ hdom f g

theorem serreTypeE6_intrinsic_root_family (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    ∃L : Subgroup (Projective CartanMatrix.E₆ K),Nat.card L=Nat.card K ∧
      ∀ (f : MulAut (Projective CartanMatrix.E₆ K)) (g : Projective CartanMatrix.E₆ K),
        ∃h : Projective CartanMatrix.E₆ K,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  have hC := E6_cartan
  change cartan
    (coordinateBase CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)=CartanMatrix.E₆ at hC
  exact exists_root_family_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan (E6_normalizer_word_identity K) hC p

theorem serreTypeE7_intrinsic_root_family (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    ∃L : Subgroup (Projective CartanMatrix.E₇ K),Nat.card L=Nat.card K ∧
      ∀ (f : MulAut (Projective CartanMatrix.E₇ K)) (g : Projective CartanMatrix.E₇ K),
        ∃h : Projective CartanMatrix.E₇ K,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  have hC := E7_cartan
  change cartan
    (coordinateBase CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₇ CartanMatrix.E₇_diag CartanMatrix.E₇_transpose
      E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)=CartanMatrix.E₇ at hC
  exact exists_root_family_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos
    K E7Signs E7_signs_square E7_signs_cartan (E7_normalizer_word_identity K) hC p

theorem serreTypeE8_intrinsic_root_family (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    ∃L : Subgroup (Projective CartanMatrix.E₈ K),Nat.card L=Nat.card K ∧
      ∀ (f : MulAut (Projective CartanMatrix.E₈ K)) (g : Projective CartanMatrix.E₈ K),
        ∃h : Projective CartanMatrix.E₈ K,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  have hC := E8_cartan
  change cartan
    (coordinateBase CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    (coordinateIndexEquiv CartanMatrix.E₈ CartanMatrix.E₈_diag CartanMatrix.E₈_transpose
      E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)=CartanMatrix.E₈ at hC
  exact exists_root_family_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos
    K E8Signs E8_signs_square E8_signs_cartan (E8_normalizer_word_identity K) hC p

theorem typeE6_intrinsic_root_family (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    ∃L : Subgroup (CFSG.Models.E6 q),Nat.card L=q.order ∧
      ∀ (f : MulAut (CFSG.Models.E6 q)) (g : CFSG.Models.E6 q),
        ∃h : CFSG.Models.E6 q,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE6_intrinsic_root_family q.Field q.prime

theorem typeE7_intrinsic_root_family (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    ∃L : Subgroup (CFSG.Models.E7 q),Nat.card L=q.order ∧
      ∀ (f : MulAut (CFSG.Models.E7 q)) (g : CFSG.Models.E7 q),
        ∃h : CFSG.Models.E7 q,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE7_intrinsic_root_family q.Field q.prime

theorem typeE8_intrinsic_root_family (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    ∃L : Subgroup (CFSG.Models.E8 q),Nat.card L=q.order ∧
      ∀ (f : MulAut (CFSG.Models.E8 q)) (g : CFSG.Models.E8 q),
        ∃h : CFSG.Models.E8 q,
          (L.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
            L.map (MulAut.conj h).toMonoidHom := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  simpa only [q.card_field] using serreTypeE8_intrinsic_root_family q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalIntrinsicRootFamily
