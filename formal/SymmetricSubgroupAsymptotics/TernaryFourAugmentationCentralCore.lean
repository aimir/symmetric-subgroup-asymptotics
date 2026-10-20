import SymmetricSubgroupAsymptotics.CentralPrimeFactorQuotientSocles
import SymmetricSubgroupAsymptotics.TernaryFourAugmentationAffineImage
import SymmetricSubgroupAsymptotics.TernaryFourBlockPermutationGenerators

/-! The actual augmentation translations form a minimal self-centralizing
core with no ambient fixed point. The absence of fixed points is proved in
the four original coordinates using explicit even permutations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryFourAugmentationCentralCore

open TernaryFourAugmentationRepresentation TernaryFourBlockPermutationGenerators
open SemidirectProduct

private def reach : Fin 4 → Equiv.Perm (Fin 4) := ![1,a,a*a,b*(a*a)]

private theorem reach_even (i : Fin 4) : reach i ∈ alternatingGroup (Fin 4) := by
  fin_cases i
  · exact (alternatingGroup (Fin 4)).one_mem
  · exact a_even
  · exact (alternatingGroup (Fin 4)).mul_mem a_even a_even
  · exact (alternatingGroup (Fin 4)).mul_mem b_even
      ((alternatingGroup (Fin 4)).mul_mem a_even a_even)

private theorem reach_zero : ∀ i : Fin 4, reach i 0 = i := by decide +kernel

theorem fixed_vector_eq_zero (R : Subgroup LinearGroup) (hR : evenHom.range ≤ R)
    (v : Vector) (hv : ∀ r : R, r.1 v = v) : v = 0 := by
  have hconstant (i : Fin 4) : encode v i = encode v 0 := by
    let g := reach i
    have hg : hom g ∈ R := hR ⟨⟨g,reach_even i⟩,rfl⟩
    have he := congrArg encode (hv ⟨hom g,hg⟩)
    change encode (hom g v) = encode v at he
    rw [encode_hom] at he
    have hi := congrFun he (g 0)
    change encode v (g.symm (g 0)) = encode v (g 0) at hi
    rw [g.symm_apply_apply,reach_zero] at hi
    exact hi.symm
  have hz : encode v 0 = 0 := by
    have hsum := encode_sum v
    have he : (∑ i : Fin 4, encode v i) = ∑ _i : Fin 4, encode v 0 :=
      Finset.sum_congr rfl (fun i _ => hconstant i)
    rw [he] at hsum
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    norm_num at hsum
    exact hsum.resolve_left (show (4 : ZMod 3) ≠ 0 by decide +kernel)
  apply encode_injective
  rw [show encode (0 : Vector) = 0 from map_zero encodeLinear]
  funext i
  exact (hconstant i).trans hz

def core (R : Subgroup LinearGroup) (hR : evenHom.range ≤ R) :
    CentralBinaryProductCore (AffineModel.Aff R) where
  V := AffineModel.Vsub R
  minimal := AffineModel.minimal (irreducible_of_even_range_le R hR)
  selfCentralizing := AffineModel.selfCentralizing R
  noFixed := by
    rintro _ ⟨w,rfl⟩ hc
    have hw : w.toAdd = 0 := by
      apply fixed_vector_eq_zero R hR
      intro r
      have he : (inr r : AffineModel.Aff R) * inl w * (inr r)⁻¹ = inl w := by
        rw [hc (inr r),mul_inv_cancel_right]
      rw [AffineModel.conj_inl] at he
      exact congrArg Multiplicative.toAdd (inl_injective he)
    have hw1 : w = 1 := Multiplicative.toAdd.injective hw
    rw [hw1,map_one]

theorem core_ne_bot (R : Subgroup LinearGroup) (hR : evenHom.range ≤ R) :
    (core R hR).V ≠ ⊥ := by
  exact AffineModel.Vsub_ne_bot_of_nonzero R
    (show (Pi.single (0 : Fin 3) (1 : ZMod 3) : Vector) ≠ 0 by
      intro h
      have he := congrFun h 0
      norm_num at he)

end SymmetricSubgroupAsymptotics.TernaryFourAugmentationCentralCore

end
