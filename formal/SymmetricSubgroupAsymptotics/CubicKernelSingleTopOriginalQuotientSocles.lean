import SymmetricSubgroupAsymptotics.CubicKernelSingleTopSocleTwo
import SymmetricSubgroupAsymptotics.OriginalKernelPrimeSectionUniform
import SymmetricSubgroupAsymptotics.OriginalKernelSectionOddRestriction
import SymmetricSubgroupAsymptotics.NormalGeneratorExtension

/-! The ternary/single-cubic-top sharing theorem applies to EVERY
original normal quotient through its literal retained kernel section. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CubicKernelSingleTopOriginalQuotientSocles
open OriginalKernelModuleChart

theorem quotientSocle {G B : Type} [Group G] [Finite G] [IsSolvable G]
    [Group B] [Finite B] (pi : G →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 3) B) [FiniteDimensional (ZMod 3) A]
    (E : OriginalKernelModuleChart pi A)
    (hu : UniformSubrepresentationGeneratorBound A.ρ 1)
    (k : ℕ) (hcard : Nat.card B∣2^k*3)
    (hB : ∀ M : Subgroup B, M.Normal →
      ∃ x : Fin 2 → B, Subgroup.normalClosure (Set.range x)=M)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  letI : IsSolvable (G ⧸ N) := solvable_of_surjective (QuotientGroup.mk'_surjective N)
  let K := E.sectionRepresentation pi A N
  letI : FiniteDimensional (ZMod 3) K := by
    change FiniteDimensional (ZMod 3) (E.sectionModule pi A N)
    infer_instance
  let s := sectionTop pi N hpi
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) x
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  have hDcard : Nat.card (G ⧸ (pi.ker ⊔ N))∣2^k*3 :=
    (Subgroup.card_dvd_of_surjective s hs).trans hcard
  have hD : SocleNormalGeneratorBound (G ⧸ (pi.ker ⊔ N)) 2 :=
    normal_generating_tuples_of_surjective s hs hB (finiteGroupSocle _) inferInstance
  exact CubicKernelSingleTopSocleTwo.socle_two (base pi N) (base_surjective pi N)
    K (E.quotientChart pi A N) (E.sectionUniform_prime pi A N hpi hu) k hDcard hD

end SymmetricSubgroupAsymptotics.CubicKernelSingleTopOriginalQuotientSocles
