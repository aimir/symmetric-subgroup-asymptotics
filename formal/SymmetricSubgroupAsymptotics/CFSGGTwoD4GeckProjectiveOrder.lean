import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageSylows
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedPositiveCardinality

/-! Actual opposite image Sylows yield the q^12 lower bound in their
central quotient. The input q^6 is the proved five-layer fixed-U count,
not a supplied G2 group-order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProjectiveOrder
open CFSGGTwoD4GeckImageSylows CFSGGTwoD4GeckFixedPositiveCardinality
variable (K : Type) [Field K] [Finite K]

local instance imageFinite : Finite (imageGroup K) :=
  Finite.of_surjective (generatedToImage K) (generatedToImage_surjective K)

theorem imagePositiveSylow_card_six (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (imagePositiveSylow K p)=Nat.card K^6 :=
  (imagePositiveSylow_card K p).trans (rootPart_card K)

theorem image_projective_order_lower (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card K^12≤Nat.card (imageGroup K⧸Subgroup.center (imageGroup K)) := by
  have hc := CFSGDisjointSylowProjectiveCardinality.card_mul_le_central_quotient
    (imagePositiveSylow K p) (imageNegativeSylow K p) (imageSylows_inf K p)
  have hn : Nat.card (imageNegativeSylow K p)=Nat.card (imagePositiveSylow K p) :=
    Nat.card_congr (Sylow.equiv (imageNegativeSylow K p) (imagePositiveSylow K p)).toEquiv
  rw [hn,imagePositiveSylow_card_six] at hc
  exact (show Nat.card K^12=Nat.card K^6*Nat.card K^6 by ring).le.trans hc

theorem imageProjective_nontrivial :
    Nontrivial (imageGroup K⧸Subgroup.center (imageGroup K)) := by
  letI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  let P := imagePositiveSylow K (ringChar K)
  have hP : 1<Nat.card P := by
    change 1<Nat.card (imagePositiveSylow K (ringChar K))
    rw [imagePositiveSylow_card_six]
    exact one_lt_pow₀ (Finite.one_lt_card (α:=K)) (by decide : (6:ℕ)≠0)
  letI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hP
  exact (CFSGDisjointSylowProjectiveCardinality.central_quotient_injective
    P (imageNegativeSylow K (ringChar K)) (imageSylows_inf K (ringChar K))).nontrivial

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProjectiveOrder
