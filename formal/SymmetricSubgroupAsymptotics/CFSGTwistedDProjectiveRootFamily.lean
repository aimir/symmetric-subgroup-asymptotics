import SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveUnipotent
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeUnipotentCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily

/-! The whole conjugate highest-root subgroup family is intrinsic in
the SAME relative central quotient. Its Sylow centre has the proved
literal fixed-field parameter, and quotient automorphisms act on the
projected Sylow without any universal-cover lifting assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeUnipotentSylow
open CFSGTwistedDRelativeHighestRoot CFSGTwistedDProjectiveUnipotent
open CFSGOrthogonalDIndexSylowCenterFamily CFSGTwistedA2FixedField

def highestRootLine (s : ℕ) (q : CFSG.PrimePower) : Subgroup (relativeRootGroup (s + 2) q) :=
  centerImage (unipotent s q)

theorem mem_highestRootLine_iff (s : ℕ) (q : CFSG.PrimePower)
    (x : relativeRootGroup (s + 2) q) :
    x ∈ highestRootLine s q ↔ ∃ a : fixedField q, x = (highestInRelativeU s q a).val := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := center_eq_highest s q z hz
    exact ⟨a, congrArg Subtype.val ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨highestInRelativeU s q a, highestInRelativeU_mem_center s q a, rfl⟩

def projectiveHighestRootLine (s : ℕ) (q : CFSG.PrimePower) : Subgroup (Projective s q) :=
  (highestRootLine s q).map (projection s q)

def projectiveConjugateRootLine (s : ℕ) (q : CFSG.PrimePower) (g : Projective s q) :
    Subgroup (Projective s q) :=
  (projectiveHighestRootLine s q).map (MulAut.conj g).toMonoidHom

theorem projectiveUnipotent_centerImage (s : ℕ) (q : CFSG.PrimePower) :
    centerImage (projectiveUnipotent s q) = projectiveHighestRootLine s q := by
  let e := unipotentProjectiveEquiv s q
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let u := e.symm z
    have hu : u ∈ Subgroup.center (unipotent s q) :=
      ((Subgroup.centerCongr e).symm ⟨z, hz⟩).property
    refine ⟨u.val, ⟨u, hu, rfl⟩, ?_⟩
    exact congrArg (fun t : projectiveUnipotent s q => (t : Projective s q))
      (e.apply_symm_apply z)
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨e v, (Subgroup.centerCongr e ⟨v, hv⟩).property, rfl⟩

theorem automorphism_maps_projectiveConjugateRootLine (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (g : Projective s q) :
    ∃ h : Projective s q,
      (projectiveConjugateRootLine s q g).map f.toMonoidHom =
        projectiveConjugateRootLine s q h := by
  letI : Finite (Projective s q) :=
    Finite.of_surjective (projection s q) (QuotientGroup.mk'_surjective _)
  obtain ⟨h, hh⟩ := exists_inner_centerImage_map q.prime (projectiveSylow s q)
    (f * MulAut.conj g)
  change (centerImage (projectiveUnipotent s q)).map (f * MulAut.conj g).toMonoidHom =
    (centerImage (projectiveUnipotent s q)).map (MulAut.conj h).toMonoidHom at hh
  rw [projectiveUnipotent_centerImage] at hh
  refine ⟨h, ?_⟩
  change ((projectiveHighestRootLine s q).map (MulAut.conj g).toMonoidHom).map
    f.toMonoidHom = _
  rw [Subgroup.map_map]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGTwistedDProjectiveRootFamily
