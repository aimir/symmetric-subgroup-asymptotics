import SymmetricSubgroupAsymptotics.CFSGSuzukiModelCardinality
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex
import Mathlib.GroupTheory.Index
import Lean.Elab.Tactic.Omega

/-! The genuine least-proper-index/order half of the Suzuki model
bound. The actual Borel has index q²+1 and is proper, so the actual least
proper index has square smaller than the proved original group order.
No outer-automorphism estimate is asserted or assumed in this file. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiLeastIndexOrder
open CFSGSuzukiUnipotent CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow
open CFSGSuzukiOppositeIntersection CFSGSuzukiModelCardinality
open PrimitiveSocleRawStructure

theorem modelBorel_card (m : ℕ) :
    Nat.card (modelBorel m)=Nat.card (CFSGSuzukiFieldParameters.Field m)^2*
      (Nat.card (CFSGSuzukiFieldParameters.Field m)-1) := by
  have hB : Nat.card (modelBorel m)=Nat.card (borelEnvelope m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (borelEnvelope_le_model m)).toEquiv
  rw [hB,borelEnvelope_card,Nat.card_units]

theorem modelBorel_index (m : ℕ) :
    (modelBorel m).index=Nat.card (CFSGSuzukiFieldParameters.Field m)^2+1 := by
  have hc := (modelBorel m).card_mul_index
  rw [model_card,←modelBorel_card] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := modelBorel m)) hc

theorem modelBorel_ne_top (m : ℕ) : modelBorel m≠⊤ := by
  intro he
  have hw : modelWeyl m∈modelBorel m := by rw [he];exact Subgroup.mem_top _
  exact weyl_not_mem_borel m hw

theorem field_card_ge_eight (m : ℕ) (hm : 1 ≤ m) :
    8 ≤ Nat.card (CFSGSuzukiFieldParameters.Field m) := by
  rw [CFSGSuzukiFieldParameters.field_card]
  exact Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3 ≤ 2*m+1)

theorem borel_index_square_lt_order {q : ℕ} (hq : 8 ≤ q) :
    (q^2+1)^2<q^2*(q-1)*(q^2+1) := by
  have ht : 2 ≤ q-1 := by omega
  have hq2 : 2 ≤ q^2 := by
    have hh : 4 ≤ q^2 := Nat.pow_le_pow_left (by omega : 2 ≤ q) 2
    omega
  have hm : q^2*2 ≤ q^2*(q-1) := Nat.mul_le_mul_left _ ht
  have hs : q^2+1<q^2*(q-1) := by omega
  have hh := Nat.mul_lt_mul_of_pos_right hs (by omega : 0<q^2+1)
  simpa only [pow_two] using hh

theorem leastProperIndex_le_borel_index (m ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) :
    ell≤Nat.card (CFSGSuzukiFieldParameters.Field m)^2+1 := by
  have hm := hell.2 (modelBorel m) (modelBorel_ne_top m)
  rwa [modelBorel_index] at hm

/-- Exactly the first numerical conclusion on the original least proper
index. This makes no claim about the still-separate Outer bound. -/
theorem leastProperIndex_square_lt_card (m : ℕ) (hm : 1 ≤ m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.Suzuki m) ell) :
    ell^2<Nat.card (CFSG.Models.Suzuki m) := by
  have hl := leastProperIndex_le_borel_index m ell hell
  have hp := Nat.pow_le_pow_left hl 2
  have hs := borel_index_square_lt_order (field_card_ge_eight m hm)
  rw [model_card]
  exact hp.trans_lt hs

theorem suzukiIndex_leastProperIndex_square_lt_card (m : ℕ) (hm : 1 ≤ m) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Index.Model (.suzuki m hm)) ell) :
    ell^2<Nat.card (CFSG.Index.Model (.suzuki m hm)) :=
  leastProperIndex_square_lt_card m hm ell hell

end SymmetricSubgroupAsymptotics.CFSGSuzukiLeastIndexOrder
