import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopMonolith
import SymmetricSubgroupAsymptotics.OriginalKernelMonolithicSocleCoinvariance

/-! The actual faithful A4/S4 quartet image forces its actual regular
Klein group to act trivially on the literal original retained section,
unless the complete quotient socle is already in the translation kernel.
No abstract monolith hypothesis or capacity premise remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalSocleCoinvariance
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R regular top)
open OriginalKernelModuleChart

theorem dichotomy {G : Type} [Group G]
    (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (l : R →* C) (ht : ∀ r, top C (l r)=regular r)
    (pi : G →* C) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) C) (E : OriginalKernelModuleChart pi A)
    (N : Subgroup G) [N.Normal] :
    finiteGroupSocle (G ⧸ N)≤(base pi N).ker ∨
      l.range≤((E.sectionRepresentation pi A N).ρ.asGroupHom.comp
        (sectionTop pi N hpi)).ker :=
  E.retained_monolith_coinvariance pi A N hpi l.range
    (BinaryPlaneFaithfulTopMonolith.range_le_nontrivial_normal C hinj heven l ht)

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulOriginalSocleCoinvariance
