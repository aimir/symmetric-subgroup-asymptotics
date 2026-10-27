import SymmetricSubgroupAsymptotics.ActualFullWreathElementaryRecurrence
import SymmetricSubgroupAsymptotics.ActualFullWreathSimpleKernelRecurrence
import SymmetricSubgroupAsymptotics.ActualFullWreathFamilyTerminal
import SymmetricSubgroupAsymptotics.PrimitiveSocleHomogeneousMinimalNormal

/-! A finite actual local-chief trace for the entire full-component
wreath family. Each constructor records a genuine local quotient and
its proved elementary or homogeneous simple coordinates. No constructor
accepts a subgroup-count inequality. The numerical cost is independent
of the permutation top and is interpreted by the proved layer counts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualFullWreathFiniteChiefCount
open PermutationalWreathProduct ActualFullWreathFamily

structure LocalGroup where
  Carrier : Type
  [group : Group Carrier]
  [finite : Finite Carrier]

attribute [instance] LocalGroup.group LocalGroup.finite

def ofType (R : Type) [Group R] [Finite R] : LocalGroup where
  Carrier := R
  group := inferInstance
  finite := inferInstance

inductive Charge where
  | elementary (dimension kernelOrder nextOrder : ℕ)
  | simple (factorCount simpleOrder automorphismOrder nextOrder : ℕ)

def Charge.multiplier (c : ℝ) (t : ℕ) : Charge → ℕ
  | .elementary a b s => b^(t*ActualFullWreathElementaryRecurrence.exponentCeiling a s t c)
  | .simple k b aut s => ActualFullWreathSimpleKernelRecurrence.multiplier k b aut s t c

inductive Trace : LocalGroup → List Charge → Prop where
  | terminal (R : LocalGroup) (hR : Subsingleton R.Carrier) : Trace R []
  | elementary (R S : LocalGroup) (phi : R.Carrier →* S.Carrier)
      (hphi : Function.Surjective phi) (C : ElementaryMinimalNormalChart phi.ker)
      (charges : List Charge) (next : Trace S charges) :
      Trace R (.elementary (Module.finrank (ZMod C.p) C.V)
        (Nat.card phi.ker) (Nat.card S.Carrier) :: charges)
  | simple (R S : LocalGroup) (T : Type) [groupT : Group T] [finiteT : Finite T]
      [simpleT : IsSimpleGroup T] (k : ℕ) (phi : R.Carrier →* S.Carrier)
      (hphi : Function.Surjective phi) (e : phi.ker ≃* (Fin k → T)) (hZ : IsCenterless T)
      (charges : List Charge) (next : Trace S charges) :
      Trace R (.simple k (Nat.card T) (Nat.card (T ≃* T)) (Nat.card S.Carrier) :: charges)

/-- Finiteness is from decreasing the ACTUAL local order. Homogeneity of
each nonabelian minimal kernel is an already proved structural theorem. -/
theorem exists_trace (R : LocalGroup) : ∃ charges : List Charge,Trace R charges := by
  have main : ∀ n : ℕ,∀ S : LocalGroup,Nat.card S.Carrier=n →
      ∃ charges : List Charge,Trace S charges := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hcard
      rcases subsingleton_or_nontrivial S.Carrier with hs | hs
      · exact ⟨[],Trace.terminal S hs⟩
      · letI : Nontrivial S.Carrier := hs
        obtain ⟨L,hL⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := S.Carrier)
        letI : L.Normal := hL.1
        let U := ofType (S.Carrier ⧸ L)
        let phi : S.Carrier →* U.Carrier := QuotientGroup.mk' L
        have hphi : Function.Surjective phi := QuotientGroup.mk'_surjective L
        have hsmall : Nat.card U.Carrier<Nat.card S.Carrier := by
          change Nat.card (S.Carrier ⧸ L)<Nat.card S.Carrier
          rw [←L.index_eq_card,←L.index_mul_card]
          exact lt_mul_of_one_lt_right
            (by rw [L.index_eq_card]; exact Nat.card_pos)
            (L.one_lt_card_iff_ne_bot.mpr hL.2.1)
        obtain ⟨charges,hcharges⟩ := ih (Nat.card U.Carrier) (hsmall.trans_eq hcard) U rfl
        have hmin : IsMinimalNormalSubgroup phi.ker := by
          change IsMinimalNormalSubgroup (QuotientGroup.mk' L).ker
          rw [QuotientGroup.ker_mk']
          exact hL
        have hlocal (K : Subgroup S.Carrier) (hK : K.Normal) (hle : K≤phi.ker) :
            K=⊥ ∨ K=phi.ker := by
          by_cases hz : K=⊥
          · exact Or.inl hz
          · exact Or.inr (hmin.2.2 K hK hz hle)
        by_cases hc : IsMulCommutative phi.ker
        · obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty phi.ker hmin.2.1 hc hlocal
          exact ⟨_,Trace.elementary S U phi hphi C charges hcharges⟩
        · obtain ⟨C⟩ := PrimitiveSocleONanScottHelpers.chart_of_minimalNormal_nonempty
            phi.ker hmin hc
          letI : Group.IsPerfect C.Simple := simple_perfect_of_nonabelian C.noncommutative
          exact ⟨_,Trace.simple S U C.Simple C.factorCount phi hphi C.equiv
            (isCenterless_of_simple_perfect C.Simple) charges hcharges⟩
  exact main (Nat.card R.Carrier) R rfl

theorem card_le_trace_product
    {Q I : Type} [Group Q] [Finite Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]
    (c : ℝ)
    (hbudget : ∀ n : ℕ,2≤n → ∀ K : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive K (Fin n) →
        (MarkedC4.genRank K : ℝ)≤c*WeakTransitiveDegreeInduction.rate n)
    (hI : 2≤Nat.card I) {R : LocalGroup} {charges : List Charge} (h : Trace R charges) :
    Nat.card (Family R.Carrier Q I)≤(charges.map (Charge.multiplier c (Nat.card I))).prod := by
  induction h with
  | terminal R hR =>
      letI : Subsingleton R.Carrier := hR
      simpa only [List.map_nil,List.prod_nil] using
        (ActualFullWreathFamilyTerminal.card_eq_one (R := R.Carrier) (Q := Q) (I := I)).le
  | elementary R S phi hphi C charges next ih =>
      have hs := ActualFullWreathElementaryRecurrence.card_le_quotient_mul
        (Q := Q) (I := I) phi hphi C c hbudget hI
      have hh := hs.trans (Nat.mul_le_mul_right _ ih)
      simpa only [List.map_cons,List.prod_cons,Charge.multiplier,Nat.mul_comm] using hh
  | simple R S T k phi hphi e hZ charges next ih =>
      have hs := ActualFullWreathSimpleKernelRecurrence.card_le_quotient_mul
        (Q := Q) (I := I) phi hphi e hZ c hbudget hI
      have hh := hs.trans (Nat.mul_le_mul_right _ ih)
      simpa only [List.map_cons,List.prod_cons,Charge.multiplier,Nat.card_fin,Nat.mul_comm] using hh

/-- The same finite list of local costs works for EVERY faithful
transitive top. The uniform constant is obtained from CFSG internally. -/
theorem exists_uniform_chief_product (hCFSG : CFSG.CFSGClassification) (R : LocalGroup) :
    ∃ c : ℝ,∃ charges : List Charge,1≤c ∧ Trace R charges ∧
      ∀ (Q I : Type) [Group Q] [Finite Q] [Fintype I] [Nonempty I]
        [MulAction Q I] [FaithfulSMul Q I] [MulAction.IsPretransitive Q I],
        2≤Nat.card I → Nat.card (Family R.Carrier Q I)≤
          (charges.map (Charge.multiplier c (Nat.card I))).prod := by
  obtain ⟨c,hc,hbudget⟩ := CFSGWeakTransitiveGeneratorBound.exists_uniform_generator_budget hCFSG
  obtain ⟨charges,htrace⟩ := exists_trace R
  refine ⟨c,charges,hc,htrace,?_⟩
  intro Q I _ _ _ _ _ _ _ hI
  exact card_le_trace_product (Q := Q) (I := I) c hbudget hI htrace

end SymmetricSubgroupAsymptotics.ActualFullWreathFiniteChiefCount
