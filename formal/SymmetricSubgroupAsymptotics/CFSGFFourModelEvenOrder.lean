import SymmetricSubgroupAsymptotics.CFSGFFourImageWeylWitness
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Even order of the ORIGINAL simple pinned F4 projective model.
Only its actual original-source action range is used for descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSG.Models.Chevalley CFSGSerreQuadraticMatrix
local instance fFourModelEvenDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem serreTypeFFour_even_card (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Even (Nat.card (Projective CartanMatrix.F₄ K)) := by
  let q := QuotientGroup.mk' (Subgroup.center (imageGroup K))
  have hne : q (imageWeyl K)≠1 := by
    intro h
    exact imageWeyl_not_center K ((QuotientGroup.eq_one_iff _).mp h)
  letI : Nontrivial (imageGroup K⧸Subgroup.center (imageGroup K)) :=
    ⟨⟨q (imageWeyl K),1,hne⟩⟩
  let e := CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (imageRepresentation realizationData K).rangeRestrict
    (imageRepresentation realizationData K).rangeRestrict_surjective
  change Even (Nat.card (Model CartanMatrix.F₄ K⧸Subgroup.center (Model CartanMatrix.F₄ K)))
  rw [Nat.card_congr e.toEquiv]
  exact imageProjective_even_card K

theorem typeFFour_even_card (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.F4 q)] :
    Even (Nat.card (CFSG.Models.F4 q)) := serreTypeFFour_even_card q.Field

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
