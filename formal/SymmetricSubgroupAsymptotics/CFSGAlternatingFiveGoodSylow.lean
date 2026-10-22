import SymmetricSubgroupAsymptotics.CFSGAlternatingFiveSylowPilot
import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.CFSGAlternatingMinimumIndex
import SymmetricSubgroupAsymptotics.PrimitiveSmallExceptionalSocleFactors

/-! The displayed Klein four is an actual Sylow subgroup of the original
A5. Its normalizer fixes its unique common fixed point and is soluble.
The sixteen distinct products with one explicit conjugate rule out a
proper generated subgroup by the actual minimum-index theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingFiveGoodSylow
open CFSGAlternatingFiveSylowPilot

def klein : Subgroup A5 where
  carrier := Set.range element
  one_mem' := ⟨0, element_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := element_mul_closed i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (element_inv i).symm⟩

def kleinEquiv : Fin 4 ≃ klein := Equiv.ofBijective
  (fun i => ⟨element i, ⟨i, rfl⟩⟩)
  ⟨fun _ _ h => element_injective (congrArg Subtype.val h), by
    rintro ⟨x, i, hi⟩
    exact ⟨i, Subtype.ext hi⟩⟩

theorem klein_card : Nat.card klein = 4 := by
  simpa only [Nat.card_fin] using (Nat.card_congr kleinEquiv).symm

theorem alternating_card : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem klein_index : klein.index = 15 := by
  have h := klein.card_mul_index
  rw [klein_card, alternating_card] at h
  omega

def twoSylow : Sylow 2 A5 :=
  (IsPGroup.of_card (show Nat.card klein = 2 ^ 2 by rw [klein_card]; decide)).toSylow
    (by rw [klein_index]; decide)

theorem twoSylow_coe : (twoSylow : Subgroup A5) = klein := rfl

theorem normalizer_le_stabilizer :
    Subgroup.normalizer (klein : Set A5) ≤ MulAction.stabilizer A5 (4 : Fin 5) := by
  intro g hg
  change (g : Equiv.Perm (Fin 5)) (4 : Fin 5) = 4
  apply (common_fixed_iff ((g : Equiv.Perm (Fin 5)) 4)).mp
  intro i
  have hm : g⁻¹ * element i * g ∈ klein :=
    ((Subgroup.mem_normalizer_iff''.mp hg) (element i)).mp ⟨i, rfl⟩
  obtain ⟨j, hj⟩ := hm
  have hx : ((g⁻¹ * element i * g : A5) : Equiv.Perm (Fin 5)) (4 : Fin 5) = 4 := by
    rw [← hj]
    exact element_fix_four j
  change (g : Equiv.Perm (Fin 5)).symm
    ((element i : Equiv.Perm (Fin 5)) ((g : Equiv.Perm (Fin 5)) 4)) = 4 at hx
  simpa only [Equiv.apply_symm_apply] using congrArg (g : Equiv.Perm (Fin 5)) hx

theorem stabilizer_card : Nat.card (MulAction.stabilizer A5 (4 : Fin 5)) = 12 := by
  letI : MulAction.IsPretransitive A5 (Fin 5) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by norm_num)
  have hi : (MulAction.stabilizer A5 (4 : Fin 5)).index = 5 := by
    simpa only [Nat.card_fin] using MulAction.index_stabilizer_of_transitive A5 (4 : Fin 5)
  have hc := (MulAction.stabilizer A5 (4 : Fin 5)).card_mul_index
  rw [hi, alternating_card] at hc
  omega

theorem normalizer_soluble : IsSolvable (Subgroup.normalizer (klein : Set A5)) := by
  apply isSolvable_of_card_dvd_small_head_degree 12 (by omega)
  have h := Subgroup.card_dvd_of_le normalizer_le_stabilizer
  rwa [stabilizer_card] at h

theorem two_conjugates_generate : Subgroup.closure ((klein : Set A5) ∪
    klein.map (MulAut.conj conjugator).toMonoidHom) = ⊤ := by
  let H := Subgroup.closure ((klein : Set A5) ∪
    klein.map (MulAut.conj conjugator).toMonoidHom)
  let f : Fin 4 × Fin 4 → H := fun z =>
    ⟨element z.1 * (conjugator * element z.2 * conjugator⁻¹),
      H.mul_mem (Subgroup.subset_closure (Or.inl ⟨z.1, rfl⟩))
        (Subgroup.subset_closure (Or.inr ⟨element z.2, ⟨z.2, rfl⟩, rfl⟩))⟩
  have hf : Function.Injective f := by
    intro z w h
    exact two_subgroup_products_injective (congrArg Subtype.val h)
  have hcard : 16 ≤ Nat.card H := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf
  change H = ⊤
  by_contra hH
  have hi := CFSGAlternatingMinimumIndex.degree_le_proper_index 5 (by decide) H hH
  have hc := H.card_mul_index
  rw [alternating_card] at hc
  nlinarith

theorem goodSylowPrime : CFSGReduction.GoodSylowPrime A5 2 := by
  refine ⟨by decide, twoSylow, conjugator, ?_, ?_⟩
  · change IsSolvable (Subgroup.normalizer (klein : Set A5))
    exact normalizer_soluble
  · change Subgroup.closure ((klein : Set A5) ∪
      klein.map (MulAut.conj conjugator).toMonoidHom) = ⊤
    exact two_conjugates_generate

end SymmetricSubgroupAsymptotics.CFSGAlternatingFiveGoodSylow
