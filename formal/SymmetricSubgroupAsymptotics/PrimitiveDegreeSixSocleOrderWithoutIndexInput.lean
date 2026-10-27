import SymmetricSubgroupAsymptotics.PrimitiveSocleSevenPointSingleFactorWithoutIndexInput
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixFiveDivisibility
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixRecognition

/-! The actual full socle of a nonaffine primitive six-point action has
one simple factor and order60 or360. The proof uses the ordinary retained
simple-index inequality, Burnside, and coset actions inside A6. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics
open PrimitiveDegreeSixRecognition

private theorem sixPoint_simpleOrder_receipt :
    ∀ n : Fin 361,n.val∣360 → 6∣n.val → 5∣n.val →
      n.val=30 ∨ n.val=60 ∨ n.val=90 ∨ n.val=120 ∨ n.val=180 ∨ n.val=360 := by
  decide +kernel

private theorem alternatingSix_subgroup_card_ne_90_120_180
    (H : Subgroup (alternatingGroup (Fin 6))) :
    Nat.card H≠90 ∧ Nat.card H≠120 ∧ Nat.card H≠180 := by
  letI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have go (hH : Nat.card H=90 ∨ Nat.card H=120 ∨ Nat.card H=180) : False := by
    have hne : H≠⊤ := by
      intro h
      have hm : Nat.card H=360 := by rw [h,Subgroup.card_top,card_alt_six]
      rcases hH with hh|hh|hh <;> omega
    have hb := simple_card_le_index_factorial H hne
    rw [card_alt_six] at hb
    have hm := H.card_mul_index
    rw [card_alt_six] at hm
    rcases hH with hh|hh|hh
    · rw [hh] at hm
      have hi : H.index=4 := by omega
      rw [hi] at hb
      norm_num [Nat.factorial] at hb
    · rw [hh] at hm
      have hi : H.index=3 := by omega
      rw [hi] at hb
      norm_num [Nat.factorial] at hb
    · rw [hh] at hm
      have hi : H.index=2 := by omega
      rw [hi] at hb
      norm_num [Nat.factorial] at hb
  exact ⟨fun h => go (Or.inl h),fun h => go (Or.inr (Or.inl h)),
    fun h => go (Or.inr (Or.inr h))⟩

namespace PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)]
    [FaithfulSMul G (Fin 6)]

theorem NonaffineData.degreeSix_socle_card_without_index
    (D : NonaffineData G (Fin 6)) :
    Nat.card (finiteGroupSocle G)=60 ∨ Nat.card (finiteGroupSocle G)=360 := by
  let S := finiteGroupSocle G
  let e : S≃*D.Simple := D.oneFactorEquiv (PrimitiveSocleSevenPointSingleFactorWithoutIndexInput.factorCount_eq_one D (by decide) (by decide))
  letI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬IsMulCommutative S := by
    intro hs
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have hh := congrArg e (hs.is_comm.comm (e.symm a) (e.symm b))
    simpa only [map_mul,e.apply_symm_apply] using hh
  letI : Group.IsPerfect S := simple_perfect_of_nonabelian hnc
  let j := perfectPermutationToAlternating (MulAction.toPermHom S (Fin 6))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom S (Fin 6)) from MulAction.toPerm_injective)
  let H := j.range
  have hH : Nat.card H=Nat.card S := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hd : Nat.card S∣360 := by
    have h := H.card_subgroup_dvd_card
    simpa only [hH,card_alt_six] using h
  letI : MulAction.IsPretransitive S (Fin 6) := D.socle_transitive
  have h6 : 6∣Nat.card S := by
    simpa only [Nat.card_fin] using degree_dvd_card_of_transitive_normal (X := Fin 6) S
  have h5 : 5∣Nat.card S := by
    by_contra h
    letI : IsSolvable S := isSolvable_of_faithful_degreeSix_not_five (G := S) (X := Fin 6) (by simp) h
    exact hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance))
  have hle : Nat.card S≤360 := Nat.le_of_dvd (by decide) hd
  rcases sixPoint_simpleOrder_receipt ⟨Nat.card S,by omega⟩ hd h6 h5 with h|h|h|h|h|h
  · change Nat.card S = 30 at h
    have hh : 60 ≤ (30 : ℕ) := h ▸ NonabelianSimpleOrderAtLeastSixty.sixty_le_card S hnc
    omega
  · exact Or.inl h
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).1 (hH.trans h)).elim
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).2.1 (hH.trans h)).elim
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).2.2 (hH.trans h)).elim
  · exact Or.inr h

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
