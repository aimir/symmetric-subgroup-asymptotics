import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Exact group equivalences transport actual character axes and their
normal quotient. This is not a transfer of a source at a different width. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

namespace LinearZmudCharacterPairData
variable {Q R : Type} [Group Q] [Group R]

def mapEquiv (D : LinearZmudCharacterPairData Q) (e : Q ≃* R) :
    LinearZmudCharacterPairData R where
  linear := D.linear.comp e.symm.toMonoidHom
  generalKernel := D.generalKernel.map e.toMonoidHom
  generalKernel_normal := D.generalKernel_normal.map e.toMonoidHom e.surjective
  generalSocleGenerator := by
    letI : (D.generalKernel.map e.toMonoidHom).Normal :=
      D.generalKernel_normal.map e.toMonoidHom e.surjective
    exact CyclicSocleQuotientTools.socleBound_equiv
      (QuotientGroup.congr D.generalKernel (D.generalKernel.map e.toMonoidHom) e rfl)
      D.generalSocleGenerator
  kernel_inf := by
    apply le_bot_iff.mp
    intro r hr
    obtain ⟨q,hq,rfl⟩ := hr.2
    have hc : D.linear q=1 := by
      have h := hr.1
      change D.linear (e.symm (e q))=1 at h
      simpa only [e.symm_apply_apply] using h
    have hm : q∈D.linear.ker ⊓ D.generalKernel := ⟨hc,hq⟩
    rw [D.kernel_inf] at hm
    simpa only [map_one] using congrArg e (Subgroup.mem_bot.mp hm)

end LinearZmudCharacterPairData

namespace PreE7B6CharacterAxisData
variable {Q R : Type} [Group Q] [Group R]

def mapEquiv (A : PreE7B6CharacterAxisData Q) (e : Q ≃* R) :
    PreE7B6CharacterAxisData R :=
  match A with
  | .oneGeneral h => .oneGeneral (CyclicSocleQuotientTools.socleBound_equiv e h)
  | .linearGeneral D => .linearGeneral (D.mapEquiv e)

end PreE7B6CharacterAxisData
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
