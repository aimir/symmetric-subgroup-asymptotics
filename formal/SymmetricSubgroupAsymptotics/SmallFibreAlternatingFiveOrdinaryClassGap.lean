import SymmetricSubgroupAsymptotics.OriginalNaturalFiveSixSmallFibreOrdinaryClassBound
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.PrimitivePermutationHalfOrderRecognition
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! An actual A5-marked simple factor pays the ordinary GM exponent on
the original small-fibre action, for every factor count and both degree
forms. Five coordinates use literal half-factorial top recognition;
larger degrees use the nonsplit unsigned binary reserve or the ternary
coordinate bound. No abstract action is replaced by a natural action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreAlternatingFiveOrdinaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

theorem binary_unsigned_gap (n : ℕ) (hn : 6≤n) :
    (12*2^(n-2))^3≤5^(2*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (12*2^((n+1)-2))^3=8*(12*2^(n-2))^3 := by
        rw [show (n+1)-2=(n-2)+1 by omega,pow_succ]
        ring
      _≤8*5^(2*n-1) := Nat.mul_le_mul_left _ ih
      _≤25*5^(2*n-1) := Nat.mul_le_mul_right _ (by decide : (8:ℕ)≤25)
      _=5^(2*(n+1)-1) := by
        rw [show 2*(n+1)-1=(2*n-1)+2 by omega,pow_add]
        ring

theorem ternary_gap (n : ℕ) (hn : 6≤n) : (3^n*10)^3≤5^(3*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3^(n+1)*10)^3=27*(3^n*10)^3 := by rw [pow_succ]; ring
      _≤27*5^(3*n-1) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-1) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-1) := by
        rw [show 3*(n+1)-1=(3*n-1)+3 by omega,pow_add]
        ring

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

theorem subnormal_class_cube_le_at_original_degree
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (e : E.Simple ≃* alternatingGroup (Fin 5))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  have hclasses : Nat.card (ConjClasses E.Simple)=
      Nat.card (ConjClasses (alternatingGroup (Fin 5))) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have houter : Nat.card (Outer E.Simple)=2 := by
    rw [outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six 5 (by decide) (by decide)
  have hB : B≤10 := by
    dsimp only [B]
    rw [hclasses,houter]
    exact Nat.mul_le_mul_right 2
      AlternatingSmallPartitionCompositionCapacity.alternating_five_class_card_le
  have hcardS : Nat.card E.Simple=60 := by
    rw [Nat.card_congr e.toEquiv]
    have hh := two_mul_nat_card_alternatingGroup (α := Fin 5)
    norm_num only [Nat.card_perm,Nat.card_fin,Nat.factorial_succ,Nat.factorial_zero] at hh
    omega
  have hindex : ∀ K : Subgroup E.Simple,K≠⊤ → 5≤K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGAlternatingMinimumIndex.degree_le_proper_index 5 (by decide)
      (K.map e.toMonoidHom) hmap
    have heindex : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heindex] at hi
    exact hi
  have hbudget : ∀ K : Subgroup E.Simple,K≠⊤ → B^3≤5^(K.index+1) := by
    intro K hK
    have hi := hindex K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (10:ℕ)^3≤5^6).trans
        (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsquare : ∀ ell : ℕ,LeastProperIndex E.Simple ell → ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGAlternatingMinimumIndex.leastProperIndex_square_lt_card 5 (by decide) ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with hgap|⟨hk,ell,hell,K,hK,hdegree,_,_⟩
  · exact hgap.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have hn : 5≤Nat.card X := by rw [hdegree]; exact hindex K hK
    have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal →
        Nat.card (ConjClasses L)≤10 := by
      intro L hL
      have hh : Nat.card (ConjClasses L)≤B := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      exact hh.trans hB
    by_cases he : Nat.card X=5
    · letI : Fintype X := Fintype.ofFinite X
      letI : DecidableEq X := Classical.decEq X
      letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
      letI : MulAction.IsPretransitive A X := source_pretransitive E
      have hnatural := PrimitivePermutationHalfOrderRecognition.alternating_or_top_of_single_factor_half_order
        (Top (A:=A) (X:=X)) E hk (by omega) (by rw [he,hcardS]; decide)
      have hTop : (Top (A:=A) (X:=X)).IsSubnormal := by
        rcases hnatural with h|h
        · rw [h]; exact Subgroup.Normal.isSubnormal inferInstance
        · rw [h]; exact Subgroup.IsSubnormal.top
      exact OriginalNaturalFiveSixSmallFibreOrdinaryClassBound.subnormal_class_cube_le_at_original_degree
        π hπ (Classical.arbitrary X) c hc (hsize _) (Or.inl he) hTop H hH
    · have hn6 : 6≤Nat.card X := by omega
      rcases hc with rfl|rfl
      · letI : Fintype X := Fintype.ofFinite X
        letI : DecidableEq X := Classical.decEq X
        have htopCard : Nat.card (Top (A:=A) (X:=X))≤120 := by
          calc
            _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
              simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
            _=120 := by rw [hcardS,houter]
        have hns : ∀ a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
          intro a ha
          have ht : Top (A:=A) (X:=X)=⊤ :=
            SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
              (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
          have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
            rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
          have hlarge : 120<(Nat.card X).factorial :=
            (by decide : 120<(6:ℕ).factorial).trans_le (Nat.factorial_le hn6)
          rw [hsym] at htopCard
          omega
        have htop11 : ∀ L : Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal →
            Nat.card (ConjClasses L)≤11 := fun L hL => (htop L hL).trans (by decide)
        have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
          π hπ (fun x=>(hsize x).le) (by omega) 11 (by decide) htop11 hns H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans (binary_unsigned_gap (Nat.card X) hn6)
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
        simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
      · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
            Nat.card (ConjClasses L)≤3 :=
          fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
        have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
          π hπ 3 hlocal 10 htop H hH
        have hh := (Nat.pow_le_pow_left hbound 3).trans (ternary_gap (Nat.card X) hn6)
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
        simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.SmallFibreAlternatingFiveOrdinaryClassGap
