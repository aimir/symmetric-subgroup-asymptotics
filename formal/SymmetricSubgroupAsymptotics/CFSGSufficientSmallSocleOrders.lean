import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeFiveSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixSocleOrder

/-! Actual five/six-point socle orders need only the unchanged order-square
component of the sufficient boundary. All coset actions, literal full socles
and finite order exclusions are retained. No sharp outer-order premise is
manufactured. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem nonabelianSimple_card_ne_thirty_of_sufficient
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnc : ¬IsMulCommutative T)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) : Nat.card T≠30 := by
  intro hT
  obtain ⟨ell,hell⟩ := PrimitiveSocleRawStructure.exists_leastProperIndex T
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hnc (isMulCommutative_iff.mpr hc)) hell.1
  have horder := (hindex T hnc ell hell).1
  rw [hT] at horder
  have he : ell=5 := by
    by_contra h
    have h6 : 6≤ell := by omega
    have h36 : 36≤ell^2 := Nat.pow_le_pow_left h6 2
    omega
  obtain ⟨H,hH,hi⟩ := hell.1
  let points : (T⧸H)≃Fin 5 := Finite.equivFinOfCardEq (by
    rw [←H.index_eq_card,hi,he])
  let f : T→*Equiv.Perm (Fin 5) := points.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom T (T⧸H))
  have hf' : Function.Injective f := points.permCongrHom.injective.comp
    (PrimitiveSocleRawStructure.simple_cosetAction_injective H hH)
  letI : Group.IsPerfect T := simple_perfect_of_nonabelian hnc
  let j := perfectPermutationToAlternating f
  have hj : Function.Injective j := perfectPermutationToAlternating_injective f hf'
  let J := j.range
  have hJ : Nat.card J=30 := (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans hT
  have hA : Nat.card (alternatingGroup (Fin 5))=60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hiJ : J.index=2 := by
    have hm := J.card_mul_index
    rw [hJ,hA] at hm
    omega
  have hJne : J≠⊤ := by
    intro h
    have hm := hJ
    rw [h,Subgroup.card_top,hA] at hm
    omega
  letI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hb := simple_card_le_index_factorial J hJne
  rw [hA,hiJ] at hb
  norm_num [Nat.factorial] at hb


end SymmetricSubgroupAsymptotics

/-! A nonaffine faithful primitive five-point action has actual full
socle order60, and actual socle quotient order at most two. The proof uses
the sign, Lagrange and the retained ordinary simple-index inequality. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

private theorem fivePoint_simpleOrder_receipt :
    ∀ n : Fin 61, n.val ∣ 60 → 25 < n.val → n.val = 30 ∨ n.val = 60 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 5)]
    [FaithfulSMul G (Fin 5)]

theorem NonaffineData.degreeFive_socle_card_of_sufficient
    (D : NonaffineData G (Fin 5)) (hindex : SufficientSimpleIndexBounds) :
    Nat.card (finiteGroupSocle G) = 60 := by
  have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex (by simp)
  let S := finiteGroupSocle G
  let e : S ≃* D.Simple := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬IsMulCommutative S := by
    intro hs
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have hh := congrArg e (hs.is_comm.comm (e.symm a) (e.symm b))
    simpa only [map_mul,e.apply_symm_apply] using hh
  letI : Group.IsPerfect S := simple_perfect_of_nonabelian hnc
  let j := perfectPermutationToAlternating (MulAction.toPermHom S (Fin 5))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom S (Fin 5)) from
      MulAction.toPerm_injective)
  let H := j.range
  have hH : Nat.card H = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hd : Nat.card S ∣ 60 := by
    have h := H.card_subgroup_dvd_card
    simpa only [hH,hA] using h
  obtain ⟨ell,hell⟩ := exists_leastProperIndex S
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hnc (isMulCommutative_iff.mpr hc)) hell.1
  have hb := (hindex S hnc ell hell).1
  have h25 : 25 < Nat.card S :=
    (Nat.pow_le_pow_left hf 2).trans_lt hb
  have hle : Nat.card S ≤ 60 := Nat.le_of_dvd (by decide) hd
  rcases fivePoint_simpleOrder_receipt ⟨Nat.card S,by omega⟩ hd h25 with ht | ht
  · exact (nonabelianSimple_card_ne_thirty_of_sufficient hnc hindex ht).elim
  · exact ht

theorem NonaffineData.degreeFive_quotient_card_le_two_of_sufficient
    (D : NonaffineData G (Fin 5)) (hindex : SufficientSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 2 := by
  have hG : Nat.card G ≤ 120 := by
    have hi := Nat.card_le_card_of_injective (MulAction.toPermHom G (Fin 5))
      (show Function.Injective (MulAction.toPermHom G (Fin 5)) from
        MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using hi
  have hm := (finiteGroupSocle G).card_mul_index
  rw [D.degreeFive_socle_card_of_sufficient hindex,Subgroup.index_eq_card] at hm
  omega

def NonaffineData.degreeFive_roundingCompression_of_sufficient
    (D : NonaffineData G (Fin 5)) (hindex : SufficientSimpleIndexBounds) :
    LocalSemisimpleRoundingCompressionData G 5 where
  E := finiteGroupSocle G
  chart := D.chart
  quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
  quotientDegree_pos := Nat.card_pos
  quotientAction := OuterWreathPermutationCompression.regularAction _
  quotientAction_injective := OuterWreathPermutationCompression.regularAction_injective _
  degree_bound := by decide
  quotientDegree_gap := by
    have hq := D.degreeFive_quotient_card_le_two_of_sufficient hindex
    rw [max_eq_left hq]
    decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure


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

omit [FaithfulSMul G (Fin 6)] in
theorem NonaffineData.degreeSix_factorCount_one_of_sufficient
    (D : NonaffineData G (Fin 6)) (hindex : SufficientSimpleIndexBounds) :
    D.factorCount=1 := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
  have horder := (hindex D.Simple D.noncommutative ell hell).1
  have hd := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  simp only [Nat.card_fin] at hd
  by_contra h
  have hk : 2≤D.factorCount := by have hp:=D.factorCount_pos;omega
  have h25 : 25≤ell^D.factorCount := calc
    25=5^2 := by decide
    _ ≤ ell^2 := Nat.pow_le_pow_left hf 2
    _ ≤ ell^D.factorCount := pow_le_pow_right₀ (by omega : 1≤ell) hk
  omega

theorem NonaffineData.degreeSix_socle_card_of_sufficient
    (D : NonaffineData G (Fin 6)) (hindex : SufficientSimpleIndexBounds) :
    Nat.card (finiteGroupSocle G)=60 ∨ Nat.card (finiteGroupSocle G)=360 := by
  let S := finiteGroupSocle G
  let e : S≃*D.Simple := D.oneFactorEquiv (D.degreeSix_factorCount_one_of_sufficient hindex)
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
  · exact (nonabelianSimple_card_ne_thirty_of_sufficient hnc hindex h).elim
  · exact Or.inl h
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).1 (hH.trans h)).elim
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).2.1 (hH.trans h)).elim
  · exact ((alternatingSix_subgroup_card_ne_90_120_180 H).2.2 (hH.trans h)).elim
  · exact Or.inr h

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
