import SymmetricSubgroupAsymptotics.SimpleOrderThreeSixty
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.CFSGAlternatingMinimumIndex
import SymmetricSubgroupAsymptotics.AlternatingSixPartitionClassCapacity
import SymmetricSubgroupAsymptotics.SmallFibreTwentyEightOrdinaryClassEnvelope
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.FullSocleSixPointSubnormalTop
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.OriginalNaturalFiveSixSmallFibreOrdinaryClassBound

/-! The exceptional abstract A6 simple factor pays the original ordinary
small-fibre class bound. The literal six-point top is recognized from
its full socle of order360; the larger actions keep their original
binary kernel or ternary coordinates. No PSL2(9) identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreAlternatingSixOrdinaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

omit [Finite A] in
private theorem source_pretransitive
    (E : NonaffineData (Top (A:=A) (X:=X)) X) : MulAction.IsPretransitive A X := by
  letI : MulAction.IsPretransitive (finiteGroupSocle (Top (A:=A) (X:=X))) X := E.socle_transitive
  constructor
  intro x y
  obtain ⟨s,hs⟩ := MulAction.exists_smul_eq (finiteGroupSocle (Top (A:=A) (X:=X))) x y
  obtain ⟨a,ha⟩ := s.val.property
  refine ⟨a,?_⟩
  change (topMap (A:=A) (X:=X) a) x=y
  rw [ha]
  exact hs

theorem subnormal_ordinary_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple≃*alternatingGroup (Fin 6))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  letI : Fintype X := Fintype.ofFinite X
  have hclasses : Nat.card (ConjClasses E.Simple)=
      Nat.card (ConjClasses (alternatingGroup (Fin 6))) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have hcardS : Nat.card E.Simple=360 := by
    rw [Nat.card_congr e.toEquiv]
    have hh := two_mul_nat_card_alternatingGroup (α:=Fin 6)
    norm_num only [Nat.card_perm,Nat.card_fin,Nat.factorial_succ,Nat.factorial_zero] at hh
    omega
  have ho : Nat.card (Outer E.Simple)≤4 := by
    rw [outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_le_four 6 (by decide)
  have hB : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤28 := by
    rw [hclasses]
    exact (Nat.mul_le_mul
      AlternatingSixPartitionClassCapacity.alternating_six_class_card_le ho).trans_eq
      (by decide : 7*4=28)
  have hindex : ∀K:Subgroup E.Simple,K≠⊤→6≤K.index := by
    intro K hK
    exact SimpleOrderThreeSixty.proper_index_ge_six hcardS K hK
  have hbudget : ∀K:Subgroup E.Simple,K≠⊤→
      (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3≤5^(K.index+1) := by
    intro K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (28:ℕ)^3≤5^7).trans
        (Nat.pow_le_pow_right (by decide) (by have hi:=hindex K hK;omega)))
  have hsquare : ∀ell:ℕ,LeastProperIndex E.Simple ell→ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGAlternatingMinimumIndex.leastProperIndex_square_lt_card 6 (by decide) ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap|⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact hgap.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have hn : 6≤Nat.card X := by rw [hdegree];exact hindex K hK
    have hn7 : Nat.card X≠7 := by
      rw [hdegree]
      exact SimpleOrderThreeSixty.proper_index_ne_seven hcardS K
    by_cases hn6 : Nat.card X=6
    · have hP : (Top (A:=A) (X:=X)).IsSubnormal :=
        FullSocleSixPointSubnormalTop.subnormal_of_order_threeSixty _ E hk hcardS hn6
      letI : MulAction.IsPretransitive A X := source_pretransitive E
      letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
      let x₀ : X := Classical.arbitrary X
      exact OriginalNaturalFiveSixSmallFibreOrdinaryClassBound.subnormal_class_cube_le_at_original_degree
        π hπ x₀ c hc (hsize x₀) (Or.inr hn6) hP H hH
    · have hn8 : 8≤Nat.card X := by omega
      have htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
          Nat.card (ConjClasses L)≤28 := by
        intro L hL
        exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hB
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
      rcases hc with rfl|rfl
      · have htopCard : Nat.card (Top (A:=A) (X:=X))≤1440 := by
          calc
            _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
              simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
            _≤360*4 := Nat.mul_le_mul hcardS.le ho
            _=1440 := by decide
        have hns : ∀a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
          intro a ha
          have ht : Top (A:=A) (X:=X)=⊤ :=
            SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
              (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
          have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
            rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
          have hlarge : 1440<(Nat.card X).factorial :=
            (by decide : 1440<(8:ℕ).factorial).trans_le (Nat.factorial_le hn8)
          rw [hsym] at htopCard
          omega
        have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
          π hπ (fun x=>(hsize x).le) (by omega) 28 (by decide) htop hns H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans
          (SmallFibreTwentyEightOrdinaryClassEnvelope.binary_ordinary (Nat.card X) hn8)
        simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
      · have hlocal : ∀x (L:Subgroup (Equiv.Perm (originalBlockFibre π x))),
            Nat.card (ConjClasses L)≤3 :=
          fun x L=>SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
        have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
          π hπ 3 hlocal 28 htop H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans
          (SmallFibreTwentyEightOrdinaryClassEnvelope.ternary_ordinary (Nat.card X) hn8)
        simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.SmallFibreAlternatingSixOrdinaryClassGap
