import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGRankOnePairAutomorphisms

/-! Actual original-derived-group automorphisms admit inner alignment
of the positive Sylow, its actual opposite and the actual derived torus.
No ordinary G2 automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedAutomorphisms
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoDerivedBruhat
open CFSGReeGTwoDerivedPairNormalizer

abbrev Derived (m : ℕ) := commutator (originalModelFixed m)

theorem map_torus_of_fix_opposite_pair (m : ℕ) (hm : 1≤m) (f : MulAut (Derived m))
    (hU : (derivedPositiveSylow m hm:Subgroup (Derived m)).map f.toMonoidHom=derivedPositiveSylow m hm)
    (hO : (derivedOpposite m hm).map f.toMonoidHom=derivedOpposite m hm) :
    (derivedTorus m).map f.toMonoidHom=derivedTorus m := by
  rw [←derived_pair_normalizer_eq_torus m hm]
  exact CFSGRankOnePairAutomorphisms.map_pair_normalizer
    (derivedPositiveSylow m hm:Subgroup (Derived m)) (derivedOpposite m hm) f hU hO

theorem exists_inner_preserve_U_opposite_torus (m : ℕ) (hm : 1≤m) (f : MulAut (Derived m)) :
    ∃g : Derived m,
      (derivedPositiveSylow m hm:Subgroup (Derived m)).map (MulAut.conj g*f).toMonoidHom=
        derivedPositiveSylow m hm ∧
      (derivedOpposite m hm).map (MulAut.conj g*f).toMonoidHom=derivedOpposite m hm ∧
      (derivedTorus m).map (MulAut.conj g*f).toMonoidHom=derivedTorus m := by
  obtain ⟨g,hU,hO⟩ := exists_inner_fix_derived_opposite_pair m hm f
  have hU' : (derivedPositiveSylow m hm:Subgroup (Derived m)).map
      (MulAut.conj g*f).toMonoidHom=derivedPositiveSylow m hm :=
    congrArg (fun P : Sylow 3 (Derived m) => P.toSubgroup) hU
  have hO' : (derivedOpposite m hm).map (MulAut.conj g*f).toMonoidHom=derivedOpposite m hm :=
    congrArg (fun P : Sylow 3 (Derived m) => P.toSubgroup) hO
  exact ⟨g,hU',hO',map_torus_of_fix_opposite_pair m hm _ hU' hO'⟩

theorem weyl_displacement_mem_torus (m : ℕ) (hm : 1≤m) (f : MulAut (Derived m))
    (hU : (derivedPositiveSylow m hm:Subgroup (Derived m)).map f.toMonoidHom=derivedPositiveSylow m hm)
    (hO : (derivedOpposite m hm).map f.toMonoidHom=derivedOpposite m hm) :
    f (derivedOpposition m hm)*(derivedOpposition m hm)⁻¹∈derivedTorus m := by
  have h := CFSGRankOnePairAutomorphisms.weyl_displacement_mem_pair_normalizer
    (derivedPositiveSylow m hm) (derivedOpposition m hm) (derivedOpposition_square m hm)
    f (Sylow.ext hU) (Sylow.ext hO)
  exact (derived_pair_normalizer_eq_torus m hm) ▸ h

end SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedAutomorphisms
