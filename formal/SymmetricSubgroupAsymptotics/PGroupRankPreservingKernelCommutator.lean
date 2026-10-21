import SymmetricSubgroupAsymptotics.PGroupElementaryAbelianizationRank

/-! Once the full original abelianization has exponent p, an actual
rank-preserving epimorphism has kernel in the original derived subgroup.
The proof compares full abelianization orders and uses the induced actual
map; it does not replace the quotient by its elementary Frattini image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]

/-- This retains the actual source, target and kernel of the epimorphism. -/
theorem pGroup_kernel_le_commutator_of_rank_preserving_abelianization_exponent
    (hG : IsPGroup p G) (q : G →* Q) (hq : Function.Surjective q)
    (hexp : ∀ a : Abelianization G, a^p=1)
    (hrank : MarkedC4.genRank Q=MarkedC4.genRank G) : q.ker ≤ commutator G := by
  let a : Abelianization G →* Abelianization Q := Abelianization.map q
  have ha : Function.Surjective a := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
    obtain ⟨g,hg⟩ := hq y
    refine ⟨Abelianization.of g,?_⟩
    change Abelianization.of (q g)=Abelianization.of y
    rw [hg]
  have hexpQ : ∀ x : Abelianization Q, x^p=1 := by
    intro x
    obtain ⟨y,rfl⟩ := ha x
    rw [← map_pow,hexp,map_one]
  have hQ := hG.of_surjective q hq
  have hcard : Nat.card (Abelianization G)=Nat.card (Abelianization Q) := by
    rw [pGroup_abelianization_card_eq_pow_genRank p hG hexp,
      pGroup_abelianization_card_eq_pow_genRank p hQ hexpQ,hrank]
  have hi : Function.Injective a :=
    (ha.bijective_of_nat_card_le hcard.le).1
  intro g hg
  rw [← Abelianization.ker_of]
  change Abelianization.of g=1
  apply hi
  change Abelianization.of (q g)=a 1
  rw [(MonoidHom.mem_ker.mp hg),map_one,map_one]

end SymmetricSubgroupAsymptotics
