import SymmetricSubgroupAsymptotics.PartitionAllDegreeSmallFibreCapacity
import SymmetricSubgroupAsymptotics.OriginalNaturalSymmetricTopOrdinaryClassBound
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.AlternatingNaturalClassExtraGap
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! Every alternating simple factor of natural size at least seven
pays the ordinary GM bound on the SAME original small-fibre action.
All factors and degree forms are retained. The literal natural top is
recognized before use; nonnatural degrees use the actual unsigned
kernel reserve and proved partition capacities, not an index gap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreAlternatingOrdinaryClassGap
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

private theorem partition_card_ge_seven (m : ℕ) (hm : 7 ≤ m) :
    7≤Nat.card (Nat.Partition m) := by
  have hfive : Nat.card (Nat.Partition 5)=7 :=
    (RestrictedPartitionCardinalityRecurrence.partition_card_eq_count 5).trans (by decide +kernel)
  have hmono : Monotone (fun n => Nat.card (Nat.Partition n)) :=
    monotone_nat_of_le_succ PartitionThreeStepRecurrence.card_le_succ
  rw [←hfive]
  exact hmono (by omega)

theorem subnormal_class_cube_le_at_original_degree
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω),π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (m : ℕ) (hm : 7 ≤ m) (e : E.Simple ≃* alternatingGroup (Fin m))
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-1) := by
  let B := Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)
  let p := Nat.card (Nat.Partition m)
  have hclasses : Nat.card (ConjClasses E.Simple)=
      Nat.card (ConjClasses (alternatingGroup (Fin m))) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have houter : Nat.card (Outer E.Simple)=2 := by
    rw [outer_card_congr e]
    exact CFSGAlternatingOuterBound.outer_card_eq_two_of_ne_six m (by omega) (by omega)
  have hpart : Nat.card (ConjClasses (alternatingGroup (Fin m)))≤p := by
    have h := AlternatingConjugacyPartitionBound.class_card_le_partitions
      (I := Fin m) (by simpa only [Fintype.card_fin] using (show 2 ≤ m by omega))
    simpa only [Fintype.card_fin] using h
  have hB : B≤2*p := by
    dsimp only [B]
    rw [hclasses,houter]
    exact (Nat.mul_le_mul_right 2 hpart).trans_eq (Nat.mul_comm _ _)
  have hindex : ∀ K : Subgroup E.Simple,K≠⊤ → m≤K.index := by
    intro K hK
    have hmap : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGAlternatingMinimumIndex.degree_le_proper_index m (by omega)
      (K.map e.toMonoidHom) hmap
    have heindex : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    rw [heindex] at hi
    exact hi
  have hweak : B^3≤5^(m+1) := by
    dsimp only [B]
    rw [hclasses,houter,mul_pow]
    calc
      _≤5^(m-2)*8 := Nat.mul_le_mul_right 8
        (AlternatingNaturalClassExtraGap.alternating_class_cube_le m (by omega))
      _≤5^(m-2)*5^3 := Nat.mul_le_mul_left _ (by decide : (8:ℕ)≤5^3)
      _=5^(m+1) := by rw [←pow_add,show (m-2)+3=m+1 by omega]
  have hbudget : ∀ K : Subgroup E.Simple,K≠⊤ → B^3≤5^(K.index+1) := by
    intro K hK
    exact hweak.trans (Nat.pow_le_pow_right (by decide) (by have hi := hindex K hK; omega))
  have hsquare : ∀ ell : ℕ,LeastProperIndex E.Simple ell → ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGAlternatingMinimumIndex.leastProperIndex_square_lt_card m (by omega) ell
      (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with hgap|⟨hk,ell,hell,K,hK,hdegree,_,_⟩
  · exact hgap.trans (Nat.pow_le_pow_right (by decide) (by omega))
  · have hn : m≤Nat.card X := by rw [hdegree]; exact hindex K hK
    have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal →
        Nat.card (ConjClasses L)≤2*p := by
      intro L hL
      have hh : Nat.card (ConjClasses L)≤B := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.subnormal_class_card_le_outer_wreath L hL
      exact hh.trans hB
    by_cases he : Nat.card X=m
    · letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
      letI : MulAction.IsPretransitive A X := source_pretransitive E
      exact OriginalNaturalSymmetricTopOrdinaryClassBound.subnormal_class_cube_le_of_single_factor_natural_degree
        π hπ (Classical.arbitrary X) c hc (hsize _) E m (by omega) e hk he H hH
    · have hnnext : m+1≤Nat.card X := by omega
      rcases hc with rfl|rfl
      · letI : Fintype X := Fintype.ofFinite X
        letI : DecidableEq X := Classical.decEq X
        letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp
          (by simpa only [Nat.card_fin] using (show 1 < m by omega))
        have htopCard : Nat.card (Top (A:=A) (X:=X)) ≤ m.factorial := by
          calc
            _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
              simpa only [hk,pow_one,Nat.factorial_one,mul_one] using E.card_le_simple_outer_wreath
            _=Nat.card (alternatingGroup (Fin m))*2 := by rw [Nat.card_congr e.toEquiv,houter]
            _=m.factorial := by
              simpa only [Nat.card_perm,Nat.card_fin,Nat.mul_comm] using
                (two_mul_nat_card_alternatingGroup (α := Fin m))
        have hns : ∀ a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
          intro a ha
          have ht : Top (A:=A) (X:=X)=⊤ :=
            SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
              (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
          have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
            rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
          have hlarge : m.factorial<(Nat.card X).factorial :=
            Nat.factorial_lt_of_lt (by omega) (by omega)
          rw [hsym] at htopCard
          omega
        have hp : 7≤p := partition_card_ge_seven m hm
        have hbound := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
          π hπ (fun x=>(hsize x).le) (by omega) (2*p) (by omega) htop hns H hH
        have hnum := PartitionAllDegreeSmallFibreCapacity.binary_capacity m hm (Nat.card X) hnnext
        have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
        simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
      · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
            Nat.card (ConjClasses L)≤3 :=
          fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
        have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
          π hπ 3 hlocal (2*p) htop H hH
        have hnum := PartitionAllDegreeSmallFibreCapacity.ternary_capacity m hm (Nat.card X) hnnext
        have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
        have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
        simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.SmallFibreAlternatingOrdinaryClassGap
