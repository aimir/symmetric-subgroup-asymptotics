import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.CFSGAlternatingGeneration
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! A nonabelian simple group with actual least index5 and its SAME
index-square order inequality is actually A5. The faithful coset action
lands in A5 by perfectness; Lagrange leaves order30/60, and order30 would
give an impossible index-two subgroup of simple A5. No model-order input,
classification catalogue or global PublishedSimpleIndexBounds is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition
open PrimitiveSocleRawStructure

private theorem divisor_sixty (m : ℕ) (hm : 25 < m) (hd : m ∣ 60) :
    m = 30 ∨ m = 60 := by
  obtain ⟨k,hk⟩ := hd
  have hk0 : k ≠ 0 := by
    intro h
    rw [h,mul_zero] at hk
    norm_num at hk
  have hk2 : k ≤ 2 := by
    by_contra hh
    have hp : 78 ≤ m*k := Nat.mul_le_mul (by omega : 26 ≤ m) (by omega : 3 ≤ k)
    rw [← hk] at hp
    omega
  have hc : k = 1 ∨ k = 2 := by omega
  rcases hc with h | h <;> rw [h] at hk <;> omega

variable (T : Type) [Group T] [Finite T] [IsSimpleGroup T]

theorem exists_mulEquiv_alternating_five (hnc : ¬ IsMulCommutative T)
    (hell : LeastProperIndex T 5) (horder : 5^2 < Nat.card T) :
    Nonempty (T ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨H,hH,hi⟩ := hell.1
  let points : (T ⧸ H) ≃ Fin 5 := Finite.equivFinOfCardEq (by rw [← H.index_eq_card,hi])
  let f : T →* Equiv.Perm (Fin 5) := points.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom T (T ⧸ H))
  have hf : Function.Injective f := points.permCongrHom.injective.comp
    (simple_cosetAction_injective H hH)
  letI : Group.IsPerfect T := simple_perfect_of_nonabelian hnc
  let j : T →* alternatingGroup (Fin 5) := perfectPermutationToAlternating f
  have hj : Function.Injective j := perfectPermutationToAlternating_injective f hf
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hd : Nat.card T ∣ 60 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_injective j hj
  have ht : Nat.card T = 60 := by
    rcases divisor_sixty (Nat.card T) (by simpa using horder) hd with ht | ht
    · let J := j.range
      have hJ : Nat.card J = 30 :=
        (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans ht
      have hiJ : J.index = 2 := by
        have hm := J.card_mul_index
        rw [hJ,hA] at hm
        omega
      have hJne : J ≠ ⊤ := by
        intro hh
        have hm := hJ
        rw [hh,Subgroup.card_top,hA] at hm
        omega
      letI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      have hb := simple_card_le_index_factorial J hJne
      rw [hA,hiJ] at hb
      norm_num [Nat.factorial] at hb
    · exact ht
  exact ⟨MulEquiv.ofBijective j ((Nat.bijective_iff_injective_and_card j).mpr
    ⟨hj,ht.trans hA.symm⟩)⟩

theorem outer_card_eq_two (hnc : ¬ IsMulCommutative T)
    (hell : LeastProperIndex T 5) (horder : 5^2 < Nat.card T) :
    Nat.card (Outer T) = 2 := by
  obtain ⟨e⟩ := exists_mulEquiv_alternating_five T hnc hell horder
  rw [CFSGReduction.outer_card_congr e]
  exact CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six 5 (by decide) (by decide)

theorem genRank_le_two (hnc : ¬ IsMulCommutative T)
    (hell : LeastProperIndex T 5) (horder : 5^2 < Nat.card T) :
    MarkedC4.genRank T ≤ 2 := by
  obtain ⟨e⟩ := exists_mulEquiv_alternating_five T hnc hell horder
  rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
  exact CFSGAlternatingGeneration.genRank_le_two 5 (by decide)

end SymmetricSubgroupAsymptotics.SimpleLeastIndexFiveRecognition
