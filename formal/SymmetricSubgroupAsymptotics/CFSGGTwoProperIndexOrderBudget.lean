import SymmetricSubgroupAsymptotics.CFSGGTwoNaturalProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGGTwoPermutationDegree

/-! A coarse original-model order ceiling suffices for the large GM
branch: the faithful natural eight-dimensional matrix group gives q^64,
and the proved original outer bound gives q^2. No group-order formula
or model recognition hypothesis is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexOrderBudget
open CFSGGTwoSerreMatrices CFSGGTwoNaturalProjectiveModel
open CFSG.Models.Chevalley PrimitiveSocleRawStructure

theorem original_order_le_matrix_space (K : Type) [Field K] [Finite K]
    (hcard : 3 ≤ Nat.card K) [IsSimpleGroup (Projective CartanMatrix.G₂ K)] :
    Nat.card (Projective CartanMatrix.G₂ K) ≤ (Nat.card K)^64 := by
  let encode : naturalGroup K → Mat K := fun g => g.val.val
  have hi : Function.Injective encode := by
    intro g h he
    exact Subtype.ext (Units.ext he)
  have hc := Nat.card_le_card_of_injective encode hi
  have hmat : Nat.card (Mat K)=(Nat.card K)^64 := by
    change Nat.card ((Fin 4 ⊕ Fin 4) → (Fin 4 ⊕ Fin 4) → K)=(Nat.card K)^64
    simp only [Nat.card_fun, Nat.card_sum, Nat.card_fin]
    norm_num
    rw [←pow_mul]
  rw [←Nat.card_congr (naturalEquivOriginal K hcard).toEquiv]
  exact hc.trans_eq hmat

theorem typeGTwo_order_mul_outer_le_proper_index_power
    (q : CFSG.PrimePower) (hsmall : q.order≠2) [IsSimpleGroup (CFSG.Models.G2 q)]
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.G2 q)*Nat.card (Outer (CFSG.Models.G2 q)) ≤ H.index^66 := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hq3 : 3 ≤ Nat.card q.Field := by rw [q.card_field]; omega
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le _)
  have hout : Nat.card (Outer (CFSG.Models.G2 q)) ≤ q.order^2 := by
    calc
      Nat.card (Outer (CFSG.Models.G2 q)) ≤ 2*q.exponent :=
        CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q
      _ ≤ 2*q.order := Nat.mul_le_mul_left 2 hf
      _ ≤ q.order*q.order := Nat.mul_le_mul_right _ hq2
      _ = q.order^2 := (pow_two _).symm
  have horder : Nat.card (CFSG.Models.G2 q) ≤ q.order^64 := by
    simpa only [q.card_field] using original_order_le_matrix_space q.Field hq3
  have hindex : q.order ≤ H.index := by
    simpa only [q.card_field] using
      CFSGGTwoPermutationDegree.field_card_le_proper_index q.Field hq3 H hH
  calc
    Nat.card (CFSG.Models.G2 q)*Nat.card (Outer (CFSG.Models.G2 q)) ≤
        q.order^64*q.order^2 := Nat.mul_le_mul horder hout
    _ = q.order^66 := (pow_add _ _ _).symm
    _ ≤ H.index^66 := Nat.pow_le_pow_left hindex _

end SymmetricSubgroupAsymptotics.CFSGGTwoProperIndexOrderBudget
