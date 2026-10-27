import SymmetricSubgroupAsymptotics.PrimitiveNineOrdinaryGeneratorsWithoutClassification
import SymmetricSubgroupAsymptotics.EightPointHalfDegreeCompleteCFSG
import SymmetricSubgroupAsymptotics.EightPointFaithfulActionHalfDegreeReduction
import SymmetricSubgroupAsymptotics.IntransitiveOrdinaryGeneratorInduction
import SymmetricSubgroupAsymptotics.TernaryBlockOrdinaryGeneratorInduction

/-! Every subgroup of the literal symmetric group on9 points has rank≤4.
The independent eight-point failed-action obstruction is discharged by
its actual proved CFSG theorem. No local IH is used to pay a different
global witness. The sole imprimitive factorization of9 is3×3. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NinePointHalfDegreeCompleteCFSG

 theorem genRank_le_four (hCFSG : CFSG.CFSGClassification)
    (J : Subgroup (Equiv.Perm (Fin 9))) : MarkedC4.genRank J≤4 := by
  have hbelow : ∀ k : ℕ,k<9→∀L : Subgroup (Equiv.Perm (Fin k)),
      (k=3→L≠⊤)→∃S : Finset L,Subgroup.closure (S : Set L)=⊤ ∧ 2*S.card≤k := by
    intro k hk L hthree
    rcases EightPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
      hCFSG k (by omega) L hthree with hpaid | hbad
    · obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := L)
      exact ⟨S,hgen,by rw [hcard]; exact hpaid⟩
    · exact (EightPointHalfDegreeCompleteCFSG.no_primitive_sporadic_counterexample_eight
        hCFSG (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono (by omega) hbad)).elim
  by_cases ht : MulAction.IsPretransitive J (Fin 9)
  swap
  · obtain ⟨S,hgen,hcard⟩ :=
      IntransitiveOrdinaryGeneratorInduction.subgroup_half_degree_generators 9 J ht hbelow
    have hr := MarkedC4.genRank_le hgen
    omega
  by_cases hp : MulAction.IsPreprimitive J (Fin 9)
  · exact PrimitiveNineOrdinaryGeneratorsWithoutClassification.genRank_le_four J hp
  letI : MulAction.IsPretransitive J (Fin 9) := ht
  let x : Fin 9 := 0
  obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) x hp
  have hprod := block.degree_product
  simp only [Nat.card_fin] at hprod
  obtain ⟨hr,htop⟩ := block.degrees_ge_two
  have hdiv : Nat.card block.Fibre ∣ 9 := ⟨Nat.card block.Points,hprod.symm⟩
  have hlt : Nat.card block.Fibre<9 := by nlinarith
  have hthree : Nat.card block.Fibre=3 := by
    have hmenu : ∀ i : Fin 9, 2 ≤ i.val → i.val ∣ 9 → i.val = 3 := by decide +kernel
    exact hmenu ⟨Nat.card block.Fibre,hlt⟩ hr hdiv
  have hrel : Nat.card block.Fibre=(MulAction.stabilizer J x).relIndex block.subgroup :=
    originalTransitiveBlockFibre_card x block.subgroup block.covers.le
  obtain ⟨S,hgen,hcard⟩ := TernaryBlockOrdinaryGeneratorInduction.subgroup_half_degree_generators
    9 J ht x block.subgroup block.covers.le block.proper (hrel.symm.trans hthree) hbelow
  have hbound := MarkedC4.genRank_le hgen
  omega

 theorem genRank_le_four_of_faithful {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hCFSG : CFSG.CFSGClassification)
    (hdegree : Nat.card X=9) : MarkedC4.genRank G≤4 := by
  let points : X ≃ Fin 9 := Finite.equivFinOfCardEq hdegree
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv (faithfulLabelledActionEquiv points)).le.trans
    (genRank_le_four hCFSG (labelledActionImage (A := G) points))

end SymmetricSubgroupAsymptotics.NinePointHalfDegreeCompleteCFSG
