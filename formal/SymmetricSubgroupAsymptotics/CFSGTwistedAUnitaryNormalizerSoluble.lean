import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNormalizerMatrices
import SymmetricSubgroupAsymptotics.CFSGUpperTriangularSoluble

/-! The SAME original upper normalizer is soluble, via the genuine
faithful natural-action pullback and the checked triangularity theorem.
No abstract Borel recognition or ambient unitary order theorem is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem originalUnipotent_normalizer_soluble (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    IsSolvable (Subgroup.normalizer (originalUnipotent r q : Set (Fixed r q))) := by
  let N := Subgroup.normalizer (originalUnipotent r q : Set (Fixed r q))
  let P := N.comap (pullbackSource r q)
  let rho : P →* Mat (q.Extension 2) r :=
    (Units.coeHom (Mat (q.Extension 2) r)).comp ((pullbackMatrix r q).comp P.subtype)
  have hinj : Function.Injective rho := by
    intro p t he
    apply Subtype.ext
    apply pullbackMatrix_injective q r
    apply Units.ext
    exact he
  have hupper (p : P) : (rho p).BlockTriangular id :=
    pullback_normalizer_upper q r hr p.val p.property
  letI : IsSolvable P := CFSGUpperUnitriangular.soluble_of_faithful_upper_matrix
    (q.Extension 2) (r + 1) P rho hinj hupper
  let f : P →* N :=
    { toFun := fun p => ⟨pullbackSource r q p.val, p.property⟩
      map_one' := by apply Subtype.ext; exact map_one (pullbackSource r q)
      map_mul' := fun p t => by apply Subtype.ext; exact map_mul (pullbackSource r q) p.val t.val }
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨p, hp⟩ := pullbackSource_surjective r hr q g.val
    refine ⟨⟨p, ?_⟩, ?_⟩
    · change pullbackSource r q p ∈ N
      rw [hp]
      exact g.property
    · exact Subtype.ext hp
  exact solvable_of_surjective (f := f) hf

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
