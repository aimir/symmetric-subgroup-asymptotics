import SymmetricSubgroupAsymptotics.SymmetricThreeDirectFactorGenerators
import SymmetricSubgroupAsymptotics.PermutationSmallDegreeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! Ordinary generators in a literal jointly faithful three-point fibre.
A proper S3 kernel image costs one generator. A full kernel image gives
an actual proved direct-product equivalence, and its S3 factor shares a
slot. No product decomposition is assumed in the statement. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ThreePointFibreOrdinaryGenerators

variable {G Q : Type} [Group G] [Finite G] [Group Q]

theorem genRank_le_max (π : G→*Q) (hπ : Function.Surjective π)
    (f : G→*Equiv.Perm (Fin 3)) (hjoint : Function.Injective (fun g:G=>(f g,π g))) :
    MarkedC4.genRank G≤ max 2 (MarkedC4.genRank Q+1) := by
  letI : Finite Q := Finite.of_surjective π hπ
  let fK : π.ker→*Equiv.Perm (Fin 3) := f.comp π.ker.subtype
  have hfK : Function.Injective fK := by
    intro x y he
    apply Subtype.ext
    apply hjoint
    apply Prod.ext
    · exact he
    · exact x.property.trans y.property.symm
  by_cases hfull:fK.range=⊤
  · let F : G→*(Equiv.Perm (Fin 3))×Q := f.prod π
    have hF : Function.Surjective F := by
      rintro ⟨s,q⟩
      obtain ⟨g,hg⟩ := hπ q
      have hm : s*(f g)⁻¹∈fK.range := by rw [hfull]; trivial
      obtain ⟨k,hk⟩ := hm
      refine ⟨k.val*g,?_⟩
      apply Prod.ext
      · change f (k.val*g)=s
        rw [map_mul]
        change fK k*f g=s
        rw [hk]
        group
      · change π (k.val*g)=q
        have hkπ : π k.val=1 := k.property
        rw [map_mul,hkπ,hg,one_mul]
    let e : G≃*(Equiv.Perm (Fin 3))×Q := MulEquiv.ofBijective F ⟨hjoint,hF⟩
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv e]
    exact SymmetricThreeDirectFactorGenerators.genRank_le_max Q
  · let eK : π.ker≃*fK.range := MonoidHom.ofInjective (f:=fK) hfK
    have hK : MarkedC4.genRank π.ker≤1 := by
      rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eK]
      have hh := PermutationSmallDegreeOrdinaryGenerators.two_mul_genRank_le_degree
        3 fK.range (by decide) (fun _=>hfull)
      omega
    have hquot : MarkedC4.genRank (G⧸π.ker)=MarkedC4.genRank Q :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (QuotientGroup.quotientKerEquivOfSurjective π hπ)
    have hh := MarkedC4.genRank_le_of_normal π.ker
    rw [hquot] at hh
    calc
      MarkedC4.genRank G≤MarkedC4.genRank π.ker+MarkedC4.genRank Q := hh
      _≤1+MarkedC4.genRank Q := Nat.add_le_add_right hK _
      _=MarkedC4.genRank Q+1 := Nat.add_comm _ _
      _≤ max 2 (MarkedC4.genRank Q+1) := le_max_right _ _

theorem exists_generating_finset (π : G→*Q) (hπ : Function.Surjective π)
    (f : G→*Equiv.Perm (Fin 3)) (hjoint : Function.Injective (fun g:G=>(f g,π g))) :
    ∃S:Finset G,Subgroup.closure (S:Set G)=⊤ ∧ S.card≤ max 2 (MarkedC4.genRank Q+1) := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G:=G)
  exact ⟨S,hgen,hS.le.trans (genRank_le_max π hπ f hjoint)⟩

end SymmetricSubgroupAsymptotics.ThreePointFibreOrdinaryGenerators
