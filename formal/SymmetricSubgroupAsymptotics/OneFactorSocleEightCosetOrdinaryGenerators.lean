import SymmetricSubgroupAsymptotics.NormalSubgroupSylowNormalizerIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex
import SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-! A subgroup of index8 supplementing the actual one-factor full socle
has faithful primitive coset action, hence the original ambient group
has rank≤3. The original group need not itself be simple or even. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OneFactorSocleEightCosetOrdinaryGenerators
open PrimitiveSocleRawStructure

theorem genRank_le_three {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] (D : NonaffineData G X) (hk : D.factorCount=1)
    (N : Subgroup G) (hN8 : N.index=8) (hsup : N ⊔ finiteGroupSocle G=⊤) :
    MarkedC4.genRank G≤3 := by
  let S := finiteGroupSocle G
  have hsupS : N ⊔ S = ⊤ := hsup
  let eS := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := eS.isSimpleGroup
  have hnS : ¬IsMulCommutative S := by
    intro hh
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have he := congrArg eS (hh.is_comm.comm (eS.symm a) (eS.symm b))
    simpa only [map_mul,eS.apply_symm_apply] using he
  have hN : N≠⊤ := by intro ht; rw [ht,Subgroup.index_top] at hN8; omega
  have hnotS : ¬S≤N := by
    intro hSN
    have ht : N=⊤ := by simpa only [sup_eq_left.mpr hSN] using hsupS
    exact hN ht
  have hcore : N.normalCore=⊥ := by
    by_contra hh
    exact hnotS ((D.oneFactor_socle_le hk N.normalCore N.normalCore_normal hh).trans N.normalCore_le)
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ N)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [←Subgroup.normalCore_eq_ker N,hcore]
  letI : FaithfulSMul G (G ⧸ N) := {
    eq_of_smul_eq_smul := by
      intro g h he
      apply hinj
      ext x
      exact he x }
  have hcoat : IsCoatom N := by
    refine ⟨hN,?_⟩
    intro L hNL
    by_contra hL
    have hLS : L ⊔ S=⊤ := top_le_iff.mp (by
      rw [←hsupS]
      exact sup_le_sup_right hNL.le S)
    have hproper : L.subgroupOf S≠⊤ := by
      intro ht
      apply hL
      have hSL : S≤L := by
        intro s hs
        have hh : (⟨s,hs⟩ : S) ∈ L.subgroupOf S := by rw [ht]; trivial
        exact hh
      simpa only [sup_eq_left.mpr hSL] using hLS
    have hmin := nonabelianSimple_proper_index_five_le
      (fun hh => hnS (isMulCommutative_iff.mpr hh)) (L.subgroupOf S) hproper
    have hidx := NormalSubgroupSylowNormalizerIndex.index_eq_of_sup_eq_top S L hLS
    rw [←hidx] at hmin
    have hmul := Subgroup.relIndex_mul_index hNL.le
    have hz : N.relIndex L≠0 := by
      intro he
      rw [he,zero_mul,hN8] at hmul
      omega
    have hone : N.relIndex L≠1 := by
      intro he
      exact hNL.not_ge ((Subgroup.relIndex_eq_one (H := N) (K := L)).mp he)
    have htwo : 2≤N.relIndex L := by omega
    have hb := Nat.mul_le_mul htwo hmin
    rw [hmul,hN8] at hb
    omega
  letI : Nontrivial (G ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [←N.index_eq_card,hN8]; decide)
  letI : MulAction.IsPreprimitive G (G ⧸ N) := by
    apply (MulAction.isCoatom_stabilizer_iff_preprimitive G ((1 : G) : G ⧸ N)).mp
    rw [MulAction.stabilizer_quotient]
    exact hcoat
  let points : (G ⧸ N) ≃ Fin 8 := Finite.equivFinOfCardEq
    (by rw [←N.index_eq_card,hN8])
  have hp : MulAction.IsPreprimitive (labelledActionImage (A := G) points) (Fin 8) :=
    (labelledAction_preprimitive_iff points).mp inferInstance
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv (faithfulLabelledActionEquiv points)).le.trans
    (PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage.genRank_le_three _ hp)

end SymmetricSubgroupAsymptotics.OneFactorSocleEightCosetOrdinaryGenerators
