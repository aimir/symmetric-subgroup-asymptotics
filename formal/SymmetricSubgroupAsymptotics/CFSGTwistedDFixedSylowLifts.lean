import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPSubgroups
import Mathlib.GroupTheory.Sylow

/-! Every Sylow of the SAME original fixed action image lifts through
the actual natural preimage to a Sylow whose literal natural matrices
are fixed. Arbitrary projectively fixed elements are not assumed fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedSylowLifts
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDFixedPSubgroups CFSGTwistedDNaturalFieldTwist CFSGSerreOrdinaryTwists

theorem exists_fixed_sylow_lift (s : ℕ) (q : CFSG.PrimePower)
    (P : Sylow q.prime (fixedImageAction s q).range) :
    ∃ Q : Sylow q.prime (naturalFixedPreimage s q),
      Q.mapSurjective (f := preimageToImage s q) (preimageToImage_surjective s q) = P ∧
      ∀ u : Q, matrixTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2)
        (u.val.val.val : Mat (q.Extension 2) (s + 4)) =
          (u.val.val.val : Mat (q.Extension 2) (s + 4)) := by
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective
    (f := preimageToImage s q) (preimageToImage_surjective s q) q.prime P
  let N := naturalFixedPreimage s q
  let L : Subgroup (elementaryRootGroup (q.Extension 2) (s + 4)) :=
    (Q : Subgroup N).map N.subtype
  have hL : IsPGroup q.prime L := Q.isPGroup'.map N.subtype
  have hLN : L ≤ naturalFixedPreimage s q := by
    rintro _ ⟨u, _, rfl⟩
    exact u.property
  refine ⟨Q, hQ, ?_⟩
  intro u
  exact pSubgroup_matrix_fixed s q L hL hLN
    ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedSylowLifts
