import SymmetricSubgroupAsymptotics.CFSGTypeARankThreeBinaryClassPacket
import SymmetricSubgroupAsymptotics.SmallFibreTwentyEightClassEnvelope
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.CFSGTypeALeastIndexSquare
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.OriginalBinaryTypeARankThreeEightClassGap
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! The actual binary rank-three factor pays all original binary fibres:
unsigned nonsplit kernel reserve handles degree>=9 and the literal
half-factorial top recognition handles degree8. Ternary degree>=9 is
paid; the SAME one-factor ternary degree8 subgroup remains explicit.
All socle factors and both actual degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryClassResidual
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

theorem subnormal_gap_or_ternary_eight
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A := A) (X := X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple ≃* CFSG.Models.A 3 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (c=3 ∧ E.factorCount=1 ∧ ∃ K : Subgroup E.Simple,
        K≠⊤ ∧ Nat.card X=K.index ∧ K.index=8) := by
  letI : IsSimpleGroup (CFSG.Models.A 3 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 3 q) := Finite.of_equiv E.Simple e.toEquiv
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hclasses : Nat.card (ConjClasses E.Simple)=Nat.card (ConjClasses (CFSG.Models.A 3 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have hB : B ≤ 28 := by
    dsimp only [B]
    rw [hclasses,outer_card_congr e]
    exact CFSGTypeARankThreeBinaryClassPacket.component_class_card_le_twentyEight q hq
  have hcardS : Nat.card E.Simple=20160 :=
    (Nat.card_congr e.toEquiv).trans (CFSGTypeARankThreeCardTwo.order_eq_20160 q hq)
  have hindex : ∀ K : Subgroup E.Simple, K≠⊤ → 8≤K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGTypeARankThreeBinaryClassPacket.proper_index_ge_eight q hq
      (K.map e.toMonoidHom) hmap
    have heindex : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heindex] at hi
    exact hi
  have hbudget : ∀ K : Subgroup E.Simple, K≠⊤ → B^3≤5^(K.index+1) := by
    intro K hK
    have hi := hindex K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (28:ℕ)^3≤5^9).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsquare : ∀ ell : ℕ, LeastProperIndex E.Simple ell → ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card 3 (by decide) q ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with hgap | ⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact Or.inl hgap
  · have hn : 8≤Nat.card X := by rw [hdegree]; exact hindex K hK
    have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
        Nat.card (ConjClasses L)≤28 := by
      intro L hL
      have hh : Nat.card (ConjClasses L)≤B := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      exact hh.trans hB
    rcases hc with rfl | rfl
    · apply Or.inl
      by_cases he : Nat.card X=8
      · letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
        letI : MulAction.IsPretransitive A X := source_pretransitive E
        exact OriginalBinaryTypeARankThreeEightClassGap.subnormal_class_cube_gap_of_single_factor_degree_eight
          π hπ (Classical.arbitrary X) (hsize _) E q hq e hk he H hH
      · have hn9 : 9≤Nat.card X := by omega
        letI : Fintype X := Fintype.ofFinite X
        letI : DecidableEq X := Classical.decEq X
        have hf : q.exponent=1 :=
          (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
            q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
            (show q.prime^q.exponent=2^1 from hq)).2
        have houter : Nat.card (Outer E.Simple)≤2 := by
          rw [outer_card_congr e]
          simpa only [hq,hf] using
            CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 3 (by decide) q
        have htopCard : Nat.card (Top (A:=A) (X:=X))≤40320 := by
          calc
            _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
              simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
            _≤20160*2 := Nat.mul_le_mul hcardS.le houter
            _=40320 := by decide
        have hns : ∀ a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
          intro a ha
          have ht : Top (A:=A) (X:=X)=⊤ :=
            SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
              (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
          have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
            rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
          have hlarge : 40320<(Nat.card X).factorial :=
            (by decide : 40320<(9:ℕ).factorial).trans_le (Nat.factorial_le hn9)
          rw [hsym] at htopCard
          omega
        have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
          π hπ (fun x=>(hsize x).le) (by omega) 28 (by decide) htop hns H hH
        have hnum := SmallFibreTwentyEightClassEnvelope.binary_unsigned_gap (Nat.card X) hn9
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
        have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
        simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
    · by_cases he : Nat.card X=8
      · exact Or.inr ⟨rfl,hk,K,hK,hdegree,by rw [←hdegree]; exact he⟩
      · have hn9 : 9≤Nat.card X := by omega
        have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
            Nat.card (ConjClasses L)≤3 :=
          fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
        have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
          π hπ 3 hlocal 28 htop H hH
        have hnum := SmallFibreTwentyEightClassEnvelope.ternary_gap (Nat.card X) hn9
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
        have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
        exact Or.inl (by simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh)

theorem binary_subnormal_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=2)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple≃*CFSG.Models.A 3 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  rcases subnormal_gap_or_ternary_eight π hπ 2 (Or.inl rfl) hsize E q hq e H hH with h|h
  · exact h
  · omega

theorem ternary_subnormal_class_cube_gap_of_nine_le
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=3) (hn : 9≤Nat.card X)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2) (e : E.Simple≃*CFSG.Models.A 3 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  rcases subnormal_gap_or_ternary_eight π hπ 3 (Or.inr rfl) hsize E q hq e H hH with h|h
  · exact h
  · obtain ⟨_,_,K,_,hdegree,hidx⟩ := h
    omega

end SymmetricSubgroupAsymptotics.SmallFibreTypeARankThreeBinaryClassResidual
