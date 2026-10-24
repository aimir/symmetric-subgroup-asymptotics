import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryIsometryClassBound
import SymmetricSubgroupAsymptotics.CFSGTwistedDBinaryIsometryClassBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGTwistedDIndexSquare
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.PrimitiveSocleModelClassCubeSquareClassBound
import Mathlib.Tactic.NormNum

/-! Actual full quadratic-isometry class bounds close the original
binary rank-four split and twisted orthogonal models. Their SAME
proper-index bounds and squared-index cardinality bounds pay every
socle factor and both original degree forms, retaining subnormality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem two_parameters (q : CFSG.PrimePower) (hq : q.order = 2) :
    q.prime = 2 ∧ q.exponent = 1 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
    q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
    (show q.prime^q.exponent = 2^1 from hq)

theorem NonaffineData.subnormal_class_cube_le_of_typeD_binary_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.D 4 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hp := two_parameters q hq
  letI : IsSimpleGroup (CFSG.Models.D 4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.D 4 q) := Finite.of_equiv D.Simple e.toEquiv
  letI : CharP q.Field 2 := Eq.mp (congrArg (fun p : ℕ => CharP q.Field p) hp.1)
    (inferInstance : CharP q.Field q.prime)
  let eM := CFSGOrthogonalDSerreMatrices.serreProjectiveEquivElementaryProjective q.Field 0
  letI : Finite (CFSGOrthogonalDSerreMatrices.elementaryProjective q.Field 4) :=
    Finite.of_equiv (CFSG.Models.D 4 q) eM.toEquiv
  have hc : Nat.card (ConjClasses (CFSG.Models.D 4 q)) ≤ 1536 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map eM.symm.toMonoidHom)
      (ConjClasses.map_surjective eM.symm.surjective)).trans
        (CFSGOrthogonalDBinaryIsometryClassBound.projective_class_card_le q.Field
          (q.card_field.trans hq))
  have ho : Nat.card (Outer (CFSG.Models.D 4 q)) ≤ 6 := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q, hp.2, mul_one] using
      typeD_four_binary_outer_card_le q hp.1
  have hi (K : Subgroup (CFSG.Models.D 4 q)) (hK : K ≠ ⊤) : 24 ≤ K.index := by
    have h := typeD_point_radical_le_proper_index 4 (by decide) q K hK
    norm_num [hq] at h
    exact (by decide : 24 ≤ 28).trans h
  have hsquare : 24^2 ≤ Nat.card (CFSG.Models.D 4 q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.D 4 q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hlo : 24 ≤ ell := (hi K hK).trans_eq he
    exact (Nat.pow_le_pow_left hlo 2).trans
      (typeD_leastProperIndex_square_lt_card 4 q (by decide) ell hell).le
  apply D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.D 4 q) e 24
    (by decide) hi _ hsquare H hH
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
    (by decide : (1536*6)^3 ≤ 5^(24-1))

theorem NonaffineData.subnormal_class_cube_le_of_typeTwistedD_binary_rank_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order = 2)
    (e : D.Simple ≃* CFSG.Models.TwistedD 4 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  have hp := two_parameters q hq
  letI : IsSimpleGroup (CFSG.Models.TwistedD 4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD 4 q) := Finite.of_equiv D.Simple e.toEquiv
  have hnc : ¬ IsMulCommutative (CFSG.Models.TwistedD 4 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hc : Nat.card (ConjClasses (CFSG.Models.TwistedD 4 q)) ≤ 3072 :=
    CFSGTwistedDBinaryIsometryClassBound.original_class_card_le q hq
  have ho : Nat.card (Outer (CFSG.Models.TwistedD 4 q)) ≤ 8 := by
    simpa only [hp.2, mul_one] using
      CFSGTwistedDOuterCardinality.original_outer_card_le_eight_exponent 0 q hnc
  have hi (K : Subgroup (CFSG.Models.TwistedD 4 q)) (hK : K ≠ ⊤) : 24 ≤ K.index := by
    have h := typeTwistedD_point_radical_le_proper_index 4 (by decide) q K hK
    norm_num [hq] at h
    exact h
  have hsquare : 24^2 ≤ Nat.card (CFSG.Models.TwistedD 4 q) := by
    obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.TwistedD 4 q)
    obtain ⟨K, hK, he⟩ := hell.1
    have hlo : 24 ≤ ell := (hi K hK).trans_eq he
    exact (Nat.pow_le_pow_left hlo 2).trans
      (typeTwistedD_leastProperIndex_square_lt_card 4 q (by decide) ell hell).le
  apply D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.TwistedD 4 q) e 24
    (by decide) hi _ hsquare H hH
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans
    (by decide : (3072*8)^3 ≤ 5^(24-1))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
