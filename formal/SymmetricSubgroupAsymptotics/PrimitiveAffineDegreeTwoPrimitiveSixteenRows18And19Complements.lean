import SymmetricSubgroupAsymptotics.BinaryFiveFrameRepresentation
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge

/-! Exact symmetric/alternating sources for the original row18/19
complements. Generation is proved with cycle and swap identities, without
enumerating either symmetric/alternating group or any normal subgroups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements

open BinaryFiveFrameRepresentation

theorem cycle_even : cycle ∈ alternatingGroup (Fin 5) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  norm_num [cycle, sign_finRotate]

theorem doubleTransposition_even : doubleTransposition ∈ alternatingGroup (Fin 5) := by
  apply Equiv.Perm.mem_alternatingGroup.mpr
  rw [doubleTransposition, map_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 5) ≠ 4)]
  norm_num

theorem symmetric_generators :
    Subgroup.closure ({cycle, transposition} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  simpa only [show finRotate 5 (0 : Fin 5) = 1 from rfl] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide : 2 ≤ 5))
      (support_finRotate_of_le (by decide : 2 ≤ 5)) (0 : Fin 5)

/-- The product of two displayed conjugate double transpositions is the
adjacent three-cycle for the square of the original five-cycle. -/
theorem triple_word :
    doubleTransposition * (cycle * doubleTransposition * cycle⁻¹) =
      Equiv.swap (3 : Fin 5) 0 * Equiv.swap 0 2 := by
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

theorem alternating_generators :
    Subgroup.closure ({cycle, doubleTransposition} : Set (Equiv.Perm (Fin 5))) =
      alternatingGroup (Fin 5) := by
  let H := Subgroup.closure ({cycle, doubleTransposition} : Set (Equiv.Perm (Fin 5)))
  have hg : cycle ∈ H := Subgroup.subset_closure (by simp)
  have hd : doubleTransposition ∈ H := Subgroup.subset_closure (by simp)
  have ht : Equiv.swap (3 : Fin 5) 0 * Equiv.swap 0 2 ∈ H := by
    rw [← triple_word]
    exact H.mul_mem hd (H.mul_mem (H.mul_mem hg hd) (H.inv_mem hg))
  have hc : cycle.IsCycle := isCycle_finRotate_of_le (by decide)
  have ho : orderOf cycle = 5 := by
    rw [hc.orderOf]
    simp [cycle, support_finRotate_of_le (by decide : 2 ≤ 5)]
  have hc2 : (cycle ^ 2).IsCycle := hc.pow_iff.mpr (by rw [ho]; decide)
  have hs2 : (cycle ^ 2).support = Finset.univ := by decide +kernel
  have hgen2 : Subgroup.closure
      ({cycle ^ 2, Equiv.swap (0 : Fin 5) 2} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
    simpa only [show (cycle ^ 2) (0 : Fin 5) = 2 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap hc2 hs2 (0 : Fin 5)
  have hsmall : Subgroup.closure
      ({cycle ^ 2, Equiv.swap (3 : Fin 5) 0 * Equiv.swap 0 2} :
        Set (Equiv.Perm (Fin 5))) = alternatingGroup (Fin 5) := by
    apply evenPairClosure_eq_alternating (by norm_num)
      (cycle ^ 2) (Equiv.swap 0 2) _ (Equiv.swap_inv _ _) hgen2
      ((alternatingGroup (Fin 5)).pow_mem cycle_even 2) hc2.ne_one
    left
    apply Equiv.ext
    intro i
    revert i
    decide +kernel
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact cycle_even
    · exact doubleTransposition_even
  · rw [← hsmall]
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact H.pow_mem hg 2
    · exact ht

abbrev R18 : Subgroup LinearGroup :=
  Subgroup.closure ({hom cycle, hom transposition} : Set LinearGroup)
abbrev R19 : Subgroup LinearGroup :=
  Subgroup.closure ({hom cycle, hom doubleTransposition} : Set LinearGroup)

theorem hom_cycle_mem18 : hom cycle ∈ R18 := Subgroup.subset_closure (by simp)
theorem hom_transposition_mem18 : hom transposition ∈ R18 := Subgroup.subset_closure (by simp)
theorem hom_cycle_mem19 : hom cycle ∈ R19 := Subgroup.subset_closure (by simp)
theorem hom_doubleTransposition_mem19 : hom doubleTransposition ∈ R19 :=
  Subgroup.subset_closure (by simp)

def evenHom : alternatingGroup (Fin 5) →* LinearGroup :=
  hom.comp (alternatingGroup (Fin 5)).subtype

theorem hom_range : hom.range = R18 := by
  rw [MonoidHom.range_eq_map, ← symmetric_generators, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

theorem evenHom_range : evenHom.range = R19 := by
  change (hom.comp (alternatingGroup (Fin 5)).subtype).range = R19
  rw [MonoidHom.range_comp, Subgroup.range_subtype, ← alternating_generators,
    MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

def complementMap18 : Equiv.Perm (Fin 5) →* R18 :=
  (MulEquiv.subgroupCongr hom_range).toMonoidHom.comp hom.rangeRestrict

def complementMap19 : alternatingGroup (Fin 5) →* R19 :=
  (MulEquiv.subgroupCongr evenHom_range).toMonoidHom.comp evenHom.rangeRestrict

theorem complementMap18_surjective : Function.Surjective complementMap18 :=
  (MulEquiv.subgroupCongr hom_range).surjective.comp hom.rangeRestrict_surjective

theorem complementMap19_surjective : Function.Surjective complementMap19 :=
  (MulEquiv.subgroupCongr evenHom_range).surjective.comp evenHom.rangeRestrict_surjective

theorem linear_normal_total18 (A B : Subgroup R18) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective complementMap18 complementMap18_surjective
    (AlternatingSymmetricNormalChain.symmetric_normal_total (by norm_num)) A B hA hB

theorem linear_normal_total19 (A B : Subgroup R19) (hA : A.Normal) (hB : B.Normal) :
    A ≤ B ∨ B ≤ A := by
  have hchain : ∀ K L : Subgroup (alternatingGroup (Fin 5)),
      K.Normal → L.Normal → K ≤ L ∨ L ≤ K :=
    AlternatingSymmetricNormalChain.alternating_normal_total
      (X := Fin 5) (by norm_num)
  exact normalSubgroups_total_of_surjective
    (G := alternatingGroup (Fin 5)) (H := R19)
    complementMap19 complementMap19_surjective hchain A B hA hB

theorem irreducible18 : AffineModel.Irreducible R18 := by
  have hle : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup ≤ R18 := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    change PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle ∈ R18
    rw [← hom_cycle]
    exact hom_cycle_mem18
  intro S hS
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.irreducible S
    (fun r hr x hx => hS r (hle hr) x hx)

theorem irreducible19 : AffineModel.Irreducible R19 := by
  have hle : PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.linearGroup ≤ R19 := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    change PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.cycle ∈ R19
    rw [← hom_cycle]
    exact hom_cycle_mem19
  intro S hS
  exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.irreducible S
    (fun r hr x hx => hS r (hle hr) x hx)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows18And19Complements
end SymmetricSubgroupAsymptotics

end
