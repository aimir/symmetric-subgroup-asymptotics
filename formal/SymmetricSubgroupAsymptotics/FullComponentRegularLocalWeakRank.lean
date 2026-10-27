import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.CFSGWeakTransitiveGeneratorBound

/-! Full local components give a transitive action on the REGULAR local
set times the original block set. Local chief quotients need not retain
the original local permutation action. Their actual regular action is
faithful, and has degree |D|*|I|. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FullComponentRegularLocalWeakRank
open PermutationalWreathProduct WeakTransitiveDegreeInduction

variable {H D Q I : Type} [Group H] [Group D] [Group Q] [MulAction Q I]

theorem regular_orbit [MulAction.IsPretransitive Q I]
    (rho : H →* PermutationalWreathProduct D Q I)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (u v : D × I) :
    ∃ h : H,rho h • u=v := by
  obtain ⟨q,hq⟩ := MulAction.exists_smul_eq Q u.2 v.2
  obtain ⟨g,hg⟩ := htop q
  have hgi : (rho g).right • u.2=v.2 := by
    change (rightHom.comp rho) g • u.2=v.2
    rw [hg]
    exact hq
  obtain ⟨k,hki,hkd⟩ := hfull v.2 (v.1*((rho g).left v.2*u.1)⁻¹)
  refine ⟨k*g,?_⟩
  rw [map_mul,mul_smul]
  apply Prod.ext
  · change (rho k).left ((rho k).right • ((rho g).right • u.2)) *
      ((rho g).left ((rho g).right • u.2)*u.1)=v.1
    rw [hgi,hki,hkd]
    group
  · change (rho k).right • ((rho g).right • u.2)=v.2
    rw [hgi,hki]

theorem rank_le_of_uniform [Finite H] [Finite D] [Finite I] [Nonempty I]
    [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]
    (C : ℝ)
    (hbudget : ∀ n : ℕ,2≤n → ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) → (MarkedC4.genRank J : ℝ)≤C*rate n)
    (rho : H →* PermutationalWreathProduct D Q I)
    (hrho : Function.Injective rho)
    (htop : Function.Surjective (rightHom.comp rho))
    (hfull : Compression.FullComponent rho) (hI : 2≤Nat.card I) :
    (MarkedC4.genRank H : ℝ)≤C*rate (Nat.card D*Nat.card I) := by
  letI : MulAction H (D × I) := MulAction.compHom (D × I) rho
  letI : FaithfulSMul H (D × I) := ⟨by
    intro g h hgh
    apply hrho
    exact eq_of_smul_eq_smul hgh⟩
  letI : MulAction.IsPretransitive H (D × I) := ⟨regular_orbit rho htop hfull⟩
  have hdegree : 2≤Nat.card (D × I) := by
    rw [Nat.card_prod]
    exact hI.trans (Nat.le_mul_of_pos_left _ Nat.card_pos)
  have hbelow : SmallerRankBound C (Nat.card (D × I)+1) := by
    intro n _ J hn hJ
    exact hbudget n hn J hJ
  have h := rank_of_faithful_transitive_action C (Nat.card (D × I)+1) hbelow
    H (D × I) hdegree (Nat.lt_succ_self _)
  simpa only [Nat.card_prod] using h

theorem exists_uniform_regular_rank (hCFSG : CFSG.CFSGClassification) :
    ∃ C : ℝ,1≤C ∧ ∀ (H D Q I : Type) [Group H] [Finite H] [Group D] [Finite D]
      [Group Q] [Finite I] [Nonempty I] [MulAction Q I] [FaithfulSMul Q I]
      [MulAction.IsPretransitive Q I],
      ∀ rho : H →* PermutationalWreathProduct D Q I,
      Function.Injective rho → Function.Surjective (rightHom.comp rho) →
      Compression.FullComponent rho → 2≤Nat.card I →
      (MarkedC4.genRank H : ℝ)≤C*rate (Nat.card D*Nat.card I) := by
  obtain ⟨C,hC,hbudget⟩ := CFSGWeakTransitiveGeneratorBound.exists_uniform_generator_budget hCFSG
  exact ⟨C,hC,fun H D Q I _ _ _ _ _ _ _ _ _ _ rho hi ht hf hI =>
    rank_le_of_uniform C hbudget rho hi ht hf hI⟩

end SymmetricSubgroupAsymptotics.FullComponentRegularLocalWeakRank
