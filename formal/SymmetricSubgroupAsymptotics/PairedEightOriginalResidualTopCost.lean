import SymmetricSubgroupAsymptotics.PairedEightAllQuotientTopCost
import SymmetricSubgroupAsymptotics.OriginalKernelUniformDualSections
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-! Every original denominator has its own exact residual top. The
published literal top costs transport to this top by the first isomorphism
theorem, including denominators which are not contained in the kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PairedEightOriginalResidualTopCost
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoPairedEightSharedTops OriginalKernelModuleChart

variable {G : Type} [Group G] (j : Fin 24)
    (pi : G →* (interface j).top) (hpi : Function.Surjective pi)
    (N : Subgroup G) [N.Normal]

theorem residual_top_surjective : Function.Surjective (sectionTop pi N hpi) := by
  intro q
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
  exact ⟨pi g,sectionTop_apply pi N hpi g⟩

def residualTopEquiv : (interface j).top ⧸ (sectionTop pi N hpi).ker ≃*
    G ⧸ (pi.ker ⊔ N) :=
  QuotientGroup.quotientKerEquivOfSurjective (sectionTop pi N hpi)
    (residual_top_surjective j pi hpi N)

include hpi in
theorem cost (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ (pi.ker ⊔ N))) : ℝ)*
      (2 : ℝ)^(((51/200 : ℝ)*naturalCapacity j)*b) ≤
    (Nat.card ((G ⧸ (pi.ker ⊔ N)) ≃* (G ⧸ (pi.ker ⊔ N))) : ℝ)*
      (2 : ℝ)^((31/16 : ℝ)*b) := by
  let e := residualTopEquiv j pi hpi N
  have hc := quotient_top_epi_mul_module_le j (sectionTop pi N hpi).ker hZmud lit b J
  have he := fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
  have ha := Nat.card_congr (MulAut.congr e).toEquiv
  rw [he,ha] at hc
  exact hc

end SymmetricSubgroupAsymptotics.PairedEightOriginalResidualTopCost
