import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenSharpClassPacket
import SymmetricSubgroupAsymptotics.CFSGPSLTwoEvenPermutationDegree
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.SmallFibreTwentySevenClassEnvelope
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGPSLTwoLeastIndexOrder

/-! Original PSL2(8) small-fibre actions retain their actual full socle
and subnormal source. The strong local−2 inequality is proved except for
the literal ternary/eight-block shape. That SAME remaining action satisfies
the ordinary global−1 inequality, so the ordinary bound is unconditional.
No nonexistent index-divisibility obstruction at8 or subgroup census is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoEightClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

omit [Finite A] in
private theorem component_budget
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=8) (e : E.Simple≃*CFSG.Models.A 1 q) :
    Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤27 := by
  letI : Finite (CFSG.Models.A 1 q) := Finite.of_equiv E.Simple e.toEquiv
  have hc : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.A 1 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  rw [hc,outer_card_congr e]
  exact CFSGPSLTwoEvenSharpClassPacket.eight_component_class_card_le_twentySeven q hq

/-- Every original strong local case is paid except the exact ternary
one-factor action on eight original blocks. The model and H are unchanged. -/
theorem subnormal_strong_gap_or_ternary_eight
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=8) (e : E.Simple≃*CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) ∨
      (c=3 ∧ E.factorCount=1 ∧ Nat.card X=8) := by
  letI : Fintype X := Fintype.ofFinite X
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 1 q) := Finite.of_equiv E.Simple e.toEquiv
  have hB := component_budget E q hq e
  have hindex : ∀K:Subgroup E.Simple,K≠⊤→8≤K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hp := (CFSGPSLTwoEvenSharpClassPacket.eight_parameters q hq).1
    have hh : q.order≤(K.map e.toMonoidHom).index := by
      simpa only [q.card_field] using
        CFSGPSLTwoEvenPermutationDegree.field_card_le_proper_index (F:=q.Field)
          ((ringChar.eq q.Field q.prime).trans hp) (K.map e.toMonoidHom) hmap
    have hi : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [hi,hq] at hh
    exact hh
  have hbudget : ∀K:Subgroup E.Simple,K≠⊤→
      (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3≤5^(K.index+1) := by
    intro K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (27:ℕ)^3≤5^9).trans
        (Nat.pow_le_pow_right (by decide) (by have hi:=hindex K hK;omega)))
  have hsquare : ∀ell:ℕ,LeastProperIndex E.Simple ell→ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGPSLTwoGeometry.leastProperIndex_square_lt_card (F:=q.Field)
      (by rw [q.card_field,hq];decide) ell (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap|⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · have hn : 8≤Nat.card X := by rw [hdegree];exact hindex K hK
    by_cases hrest : c=3 ∧ Nat.card X=8
    · exact Or.inr ⟨hrest.1,hk,hrest.2⟩
    · left
      have htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
          Nat.card (ConjClasses L)≤27 := by
        intro L hL
        exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hB
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
      rcases hc with rfl|rfl
      · have hcardS : Nat.card E.Simple=504 :=
          (Nat.card_congr e.toEquiv).trans (CFSGPSLTwoEvenSharpClassPacket.eight_order_eq_504 q hq)
        have ho : Nat.card (Outer E.Simple)≤3 := by
          rw [outer_card_congr e]
          exact CFSGPSLTwoEvenSharpClassPacket.eight_outer_card_le_three q hq
        have htopCard : Nat.card (Top (A:=A) (X:=X))≤1512 := by
          calc
            _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
              simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
            _≤504*3 := Nat.mul_le_mul hcardS.le ho
            _=1512 := by decide
        have hns : ∀a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
          intro a ha
          have ht : Top (A:=A) (X:=X)=⊤ :=
            SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
              (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
          have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
            rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
          have hlarge : 1512<(Nat.card X).factorial :=
            (by decide : 1512<(8:ℕ).factorial).trans_le (Nat.factorial_le hn)
          rw [hsym] at htopCard
          omega
        have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
          π hπ (fun x=>(hsize x).le) (by omega) 27 (by decide) htop hns H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans
          (SmallFibreTwentySevenClassEnvelope.binary_gap (Nat.card X) hn)
        simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
      · have hlocal : ∀x (L:Subgroup (Equiv.Perm (originalBlockFibre π x))),
            Nat.card (ConjClasses L)≤3 :=
          fun x L=>SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
        have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
          π hπ 3 hlocal 27 htop H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans
          (SmallFibreTwentySevenClassEnvelope.ternary_gap (Nat.card X) (by omega))
        simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

/-- The original ordinary GM exponent−1 holds for ALL actual small-fibre
PSL2(8) actions, including the retained ternary/eight local−2 seam. -/
theorem subnormal_ordinary_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=8) (e : E.Simple≃*CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  rcases subnormal_strong_gap_or_ternary_eight π hπ c hc hsize E q hq e H hH with
      hgap|⟨hc3,hk,hn8⟩
  · exact hgap.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have hsize3 : ∀x,Nat.card (originalBlockFibre π x)=3 :=
      fun x=>(hsize x).trans hc3
    have hB := component_budget E q hq e
    have htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
        Nat.card (ConjClasses L)≤27 := by
      intro L hL
      exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hB
    have hlocal : ∀x (L:Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L)≤3 :=
      fun x L=>SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize3 x).le L
    have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal 27 htop H hH
    have hh := (Nat.pow_le_pow_left hbound 3).trans
      (SmallFibreTwentySevenClassEnvelope.ternary_ordinary (Nat.card X) (by omega))
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize3
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoEightClassGap
