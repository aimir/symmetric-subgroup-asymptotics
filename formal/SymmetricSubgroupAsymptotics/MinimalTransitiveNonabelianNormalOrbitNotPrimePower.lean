import SymmetricSubgroupAsymptotics.IntravariantNormalizerOrbitTransitivity
import SymmetricSubgroupAsymptotics.SylowPrimePowerTransitive
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerGeneration
import SymmetricSubgroupAsymptotics.MinimalNormalSimpleQuotients
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.GroupTheory.Nilpotent

/-! Elementary exclusion of prime-power orbits of an actual nonabelian
minimal normal subgroup in a minimally transitive faithful action.
No CFSG, odd-order, simple-index classification, or Tracey input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.MinimalTransitiveNonabelianNormalOrbitNotPrimePower
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
  [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem orbit_card_ne_prime_power
    (hmin : ∀ N : Subgroup G, MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) (hL : IsMinimalNormalSubgroup L)
    (hnc : ¬ IsMulCommutative L) (p r : ℕ) [Fact p.Prime] (x₀ : X) :
    Nat.card (MulAction.orbit L x₀) ≠ p^r := by
  intro hcard
  letI : L.Normal := hL.1
  let P : Sylow p L := Classical.choice inferInstance
  have hcards (x : X) : Nat.card (MulAction.orbit L x)=p^r := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x₀ x
    change (MulAction.orbit L x).ncard=p^r
    rw [←hg,←MulAction.smul_orbit_eq_orbit_smul L x₀ g,Set.ncard_smul_set]
    exact hcard
  have hmove (x : X) (l : L) : ∃ k : P, ((k.val : L) : G) • x=(l : G) • x := by
    let x' : MulAction.orbit L x := ⟨x,MulAction.mem_orbit_self x⟩
    let y' : MulAction.orbit L x := ⟨l • x,MulAction.mem_orbit x l⟩
    letI : Nonempty (MulAction.orbit L x) := ⟨x'⟩
    letI : MulAction.IsPretransitive L (MulAction.orbit L x) := ⟨by
      intro y z
      obtain ⟨a,ha⟩ := MulAction.mem_orbit_iff.mp y.property
      obtain ⟨b,hb⟩ := MulAction.mem_orbit_iff.mp z.property
      refine ⟨b*a⁻¹,Subtype.ext ?_⟩
      change (b*a⁻¹) • y.val=z.val
      rw [←ha,mul_smul,inv_smul_smul,hb]⟩
    letI : MulAction.IsPretransitive P (MulAction.orbit L x) :=
      sylow_isPretransitive_of_card_eq_prime_pow P (hcards x)
    obtain ⟨k,hk⟩ := MulAction.exists_smul_eq P x' y'
    exact ⟨k,congrArg Subtype.val hk⟩
  let H : Subgroup G := (P : Subgroup L).map L.subtype
  have hloc (x : X) (l : L) : ∃ k : L,
      k.val ∈ Subgroup.normalizer (H : Set G) ∧ k.val • x=l.val • x := by
    obtain ⟨k,hk⟩ := hmove x l
    have hmem : ((k.val : L) : G) ∈ H := ⟨k.val,k.property,rfl⟩
    exact ⟨k.val,H.le_normalizer hmem,hk⟩
  have hHnormal : H.Normal :=
    IntravariantNormalizerOrbitTransitivity.mapped_subgroup_normal_of_minimal_transitive
      hmin L (P : Subgroup L) (sylow_intravariant P) hloc
  by_cases hz : H=⊥
  · have hLb : L=⊥ := by
      apply bot_unique
      intro l hl
      change l=1
      apply FaithfulSMul.eq_of_smul_eq_smul (α:=X)
      intro x
      obtain ⟨k,hk⟩ := hmove x ⟨l,hl⟩
      have hmem : ((k.val : L) : G) ∈ H := ⟨k.val,k.property,rfl⟩
      have hke : ((k.val : L) : G)=1 := Subgroup.mem_bot.mp (hz ▸ hmem)
      simpa only [hke,one_smul] using hk.symm
    exact hL.2.1 hLb
  · have hHL : H=L := hL.2.2 H hHnormal hz (Subgroup.map_subtype_le _)
    have hPtop : (P : Subgroup L)=⊤ := by
      apply Subgroup.map_injective L.subtype_injective
      simpa only [H,←MonoidHom.range_eq_map,Subgroup.range_subtype] using hHL
    have honto : Function.Surjective (P : Subgroup L).subtype := by
      intro l
      exact ⟨⟨l,hPtop.symm ▸ Subgroup.mem_top l⟩,rfl⟩
    have hpL : IsPGroup p L := P.isPGroup'.of_surjective (P : Subgroup L).subtype honto
    letI : Group.IsNilpotent L := hpL.isNilpotent
    letI : IsSolvable L := inferInstance
    letI : Nontrivial L := L.nontrivial_iff_ne_bot.mpr hL.2.1
    letI : Group.IsPerfect L := nonabelian_minimal_normal_perfect L (by
      intro K hK hKL
      by_cases hb : K=⊥
      · exact Or.inl hb
      · exact Or.inr (hL.2.2 K hK hb hKL)) hnc
    exact Group.IsPerfect.not_isSolvable L inferInstance

theorem orbit_card_ne_two_power
    (hmin : ∀ N : Subgroup G, MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) (hL : IsMinimalNormalSubgroup L)
    (hnc : ¬ IsMulCommutative L) (r : ℕ) (x : X) :
    Nat.card (MulAction.orbit L x) ≠ 2^r := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orbit_card_ne_prime_power hmin L hL hnc 2 r x

end SymmetricSubgroupAsymptotics.MinimalTransitiveNonabelianNormalOrbitNotPrimePower
