import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCrossShapeRootCommutation

/-! The recovered signed root permutation is rigid. Actual root-group
cardinalities preserve the paired/singleton classes; their unique
noncommuting cross-edge fixes the two middle labels and then all four.
This works in characteristic two and uses no Dynkin-classification input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootRigidity
open CFSGTwistedE6GeckSignedRootCardinality CFSGTwistedE6GeckCrossShapeRootCommutation
open CFSGTwistedE6GeckOriginalSignedRootAction CFSGTwistedE6GeckOriginalRankOneWitness
open CFSGTwistedE6GeckOriginalRootIntersection CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckOriginalOppositeAlignment

theorem signed_root_permutation_eq_one (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (sigma : Equiv.Perm (Fin 4))
    (hsigma : ∀neg a,(originalSignedRoot q neg a).map f.toMonoidHom=
      originalSignedRoot q neg (sigma a)) : sigma=1 := by
  have hshape := root_permutation_preserves_shape q f sigma (hsigma false)
  have hp : (sigma 1).val<2 := (hshape 1).mpr (by decide)
  have hs : 2≤(sigma 2).val := by
    by_contra h
    have hh := (hshape 2).mp (show (sigma 2).val<2 from by omega)
    norm_num at hh
  have hmiddle : sigma 1=1 ∧ sigma 2=2 := by
    by_contra h
    have hedge : sigma 1≠1 ∨ sigma 2≠2 := not_and_or.mp h
    have hmem1 : f (originalOrbitOne q false 1)∈originalOrbitRoot q (sigma 1) := by
      change f (originalOrbitOne q false 1)∈originalSignedRoot q false (sigma 1)
      rw [←hsigma false 1]
      exact ⟨originalOrbitOne q false 1,originalOrbitOne_positive_mem q 1,rfl⟩
    have hmem2 : f (originalOrbitOne q false 2)∈originalOrbitRoot q (sigma 2) := by
      change f (originalOrbitOne q false 2)∈originalSignedRoot q false (sigma 2)
      rw [←hsigma false 2]
      exact ⟨originalOrbitOne q false 2,originalOrbitOne_positive_mem q 2,rfl⟩
    have hc := original_cross_shape_commute q (sigma 1) (sigma 2) hp hs hedge _ hmem1 _ hmem2
    have he : originalOrbitOne q false 1*originalOrbitOne q false 2=
        originalOrbitOne q false 2*originalOrbitOne q false 1 :=
      f.injective (by simpa only [map_mul] using hc.eq)
    exact original_middle_not_commute q he
  have hzero : sigma 0=0 := by
    have hlt : (sigma 0).val<2 := (hshape 0).mpr (by decide)
    have hne : (sigma 0).val≠1 := by
      intro hv
      have he : sigma 0=sigma 1 := (Fin.ext hv).trans hmiddle.1.symm
      exact (by decide : (0 : Fin 4)≠1) (sigma.injective he)
    apply Fin.ext
    change (sigma 0).val=0
    omega
  have hthree : sigma 3=3 := by
    have hge : 2≤(sigma 3).val := by
      by_contra h
      have hh := (hshape 3).mp (show (sigma 3).val<2 from by omega)
      norm_num at hh
    have hne : (sigma 3).val≠2 := by
      intro hv
      have he : sigma 3=sigma 2 := (Fin.ext hv).trans hmiddle.2.symm
      exact (by decide : (3 : Fin 4)≠2) (sigma.injective he)
    apply Fin.ext
    change (sigma 3).val=3
    have hlt := (sigma 3).isLt
    omega
  apply Equiv.ext
  intro i
  fin_cases i
  · exact hzero
  · exact hmiddle.1
  · exact hmiddle.2
  · exact hthree

theorem original_pair_stabilizer_fixes_signed_roots (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∀neg a,(originalSignedRoot q neg a).map f.toMonoidHom=originalSignedRoot q neg a := by
  obtain ⟨sigma,hsigma⟩ := exists_original_signed_root_permutation q f hU hV
  have he := signed_root_permutation_eq_one q f sigma hsigma
  subst sigma
  exact hsigma

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootRigidity
