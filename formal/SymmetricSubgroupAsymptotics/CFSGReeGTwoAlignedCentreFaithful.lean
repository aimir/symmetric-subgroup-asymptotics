import SymmetricSubgroupAsymptotics.CFSGReeGTwoPairTorusEquivariance
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestrictionFaithful
import SymmetricSubgroupAsymptotics.CFSGReeGTwoSquaredTorusRigidity

/-! The actual opposed-pair stabilizer embeds faithfully into the
square-scalar normalizer on the central field axis. Intrinsic positive
rigidity and the faithful actual Sylow action discharge both kernels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreFaithful
open CFSGReeGTwoFieldParameters CFSGReeGTwoPairRestriction
open CFSGReeGTwoPairRestrictionFaithful CFSGReeGTwoAlignedCentreAction
open CFSGReeGTwoPairTorusEquivariance CFSGReeGTwoPositiveAutomorphismLayers
open CFSGReeGTwoPositiveCentre CFSGReeGTwoOriginalPositiveSubgroup

theorem alignedCentreAction_injective (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] : Function.Injective (alignedCentreAction m hm) := by
  apply (MonoidHom.ker_eq_bot_iff (alignedCentreAction m hm)).mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  have hf' : alignedCentreAction m hm f=1 := hf
  have hcentre (d : Field m) :
      pairRestriction m hm f (centralHom m (Multiplicative.ofAdd d))=
        centralHom m (Multiplicative.ofAdd d) := by
    have h := centralAction_intertwine m (pairRestriction m hm f) d
    change pairRestriction m hm f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd (alignedCentreAction m hm f d)) at h
    rw [hf'] at h
    exact h
  have hcomm (t : (Field m)ˣ) (u : fixedPositiveGroup m) :
      pairRestriction m hm f (CFSGReeGTwoPositiveDerived.fixedPositiveTorusAut m (t^2) u)=
      CFSGReeGTwoPositiveDerived.fixedPositiveTorusAut m (t^2) (pairRestriction m hm f u) :=
    congrArg (fun A:MulAut (fixedPositiveGroup m)=>A u)
      (pairRestriction_commutes_square_torus m hm f hf' t)
  have hU := CFSGReeGTwoSquaredTorusRigidity.eq_one_of_center_fixed_square_torus
    m hm (pairRestriction m hm f) hcentre hcomm
  exact pairRestriction_injective m hm
    (hU.trans (map_one (pairRestriction m hm)).symm)

theorem alignedCentreNormalizerHom_injective (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Function.Injective (alignedCentreNormalizerHom m hm) := by
  intro f g he
  apply alignedCentreAction_injective m hm
  exact congrArg Subtype.val he

theorem pairStabilizer_card_le (m : ℕ) (hm : 1≤m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] :
    Nat.card (pairStabilizer m hm)≤Nat.card (Field m)ˣ*Nat.card (Field m≃+*Field m) := by
  letI : Finite (AddAut (Field m)) :=
    Finite.of_injective (fun A:AddAut (Field m)=>(A:Field m→Field m)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective (alignedCentreNormalizerHom m hm)
    (alignedCentreNormalizerHom_injective m hm)).trans
      (CFSGFiniteFieldScalarNormalizer.card_squareScalarNormalizer_le (Field m))

end SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreFaithful
