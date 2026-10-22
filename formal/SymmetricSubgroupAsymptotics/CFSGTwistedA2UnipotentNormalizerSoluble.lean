import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentNormalizerMatrices
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble

/-! The actual original unipotent normalizer is soluble, by the faithful
upper-triangular matrix action of its genuine natural-action pullback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices CFSGTwistedA2OriginalRelations
open CFSG.Models.Chevalley CFSGSerreFixedRootElements

theorem twistedFixedAction_two_injective (q : CFSG.PrimePower) :
    Function.Injective (twistedFixedAction 2 q) := by
  intro g h he
  have hh := naturalAction_injective (q.Extension 2) he
  apply Subtype.ext
  exact congrArg (fun u : Model A (q.Extension 2) => u.val) hh

theorem pullbackMatrix_two_injective (q : CFSG.PrimePower) :
    Function.Injective (pullbackMatrix 2 q) := by
  intro p t he
  have helem : pullbackElementary 2 q p = pullbackElementary 2 q t := by
    apply Subtype.ext
    exact he
  have hsource : pullbackSource 2 q p = pullbackSource 2 q t := by
    apply twistedFixedAction_two_injective q
    rw [← pullback_action_eq, ← pullback_action_eq, helem]
  apply Subtype.ext
  exact Prod.ext hsource helem

theorem originalUnipotent_normalizer_soluble (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    IsSolvable (Subgroup.normalizer (originalUnipotent q : Set (OriginalFixedA 2 q))) := by
  let N := Subgroup.normalizer (originalUnipotent q : Set (OriginalFixedA 2 q))
  let P := N.comap (pullbackSource 2 q)
  let rho : P →* Mat (q.Extension 2) 2 :=
    (Units.coeHom (Mat (q.Extension 2) 2)).comp
      ((pullbackMatrix 2 q).comp P.subtype)
  have hinj : Function.Injective rho := by
    intro p t he
    apply Subtype.ext
    apply pullbackMatrix_two_injective q
    apply Units.ext
    exact he
  have hupper (p : P) : (rho p).BlockTriangular id :=
    pullback_normalizer_upper q hq p.val p.property
  letI : IsSolvable P :=
    CFSGUpperUnitriangular.soluble_of_faithful_upper_matrix (q.Extension 2) 3 P rho hinj hupper
  let f : P →* N :=
    { toFun := fun p => ⟨pullbackSource 2 q p.val, p.property⟩
      map_one' := by apply Subtype.ext; exact map_one (pullbackSource 2 q)
      map_mul' := fun p t => by apply Subtype.ext; exact map_mul (pullbackSource 2 q) p.val t.val }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨p, hp⟩ := pullbackSource_surjective 2 (by decide) q g.val
    refine ⟨⟨p, ?_⟩, ?_⟩
    · change pullbackSource 2 q p ∈ N
      rw [hp]
      exact g.property
    · apply Subtype.ext
      exact hp
  exact solvable_of_surjective (f := f) hf

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
