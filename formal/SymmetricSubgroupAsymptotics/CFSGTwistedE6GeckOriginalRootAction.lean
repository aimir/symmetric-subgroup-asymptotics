import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalOppositeParabolics
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! Preserving the ORIGINAL opposed Sylow pair forces a permutation of
the actual four positive singleton/paired root charts. They are recovered
as intersections with intrinsic opposite minimal parabolics. No original
automorphism is lifted, and no folded abelianization is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootAction
open CFSGTwistedE6GeckOriginalOppositeParabolics CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalPairAlignment CFSGMinimalOvergroupAutomorphismAction

theorem exists_original_opposite_parabolic_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃sigma : Equiv.Perm (Fin 4),∀a : Fin 4,
      (originalOppositeParabolic q a).map f.toMonoidHom=originalOppositeParabolic q (sigma a) := by
  have hB : (Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q))).map
      f.toMonoidHom=Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q)) :=
    (Subgroup.map_equiv_normalizer_eq (originalNegative q) f).trans
      (congrArg (fun S : Subgroup (CFSG.Models.TwistedE6 q)=>
        Subgroup.normalizer (S : Set (CFSG.Models.TwistedE6 q))) hV)
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalNegative q : Set (CFSG.Models.TwistedE6 q)))
    (originalOppositeParabolic q) (original_lower_lt_oppositeParabolic q)
    (original_oppositeParabolic_minimal q) (original_minimal_overgroup_eq_oppositeParabolic q)
    (originalOppositeParabolic_injective q) f hB

theorem exists_original_root_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)))
    (hV : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃sigma : Equiv.Perm (Fin 4),∀a : Fin 4,
      (originalOrbitRoot q a).map f.toMonoidHom=originalOrbitRoot q (sigma a) := by
  obtain ⟨sigma,hsigma⟩ := exists_original_opposite_parabolic_permutation q f hV
  refine ⟨sigma,fun a=>?_⟩
  rw [←original_positive_inf_oppositeParabolic q a,
    Subgroup.map_inf _ _ _ f.injective,hU,hsigma a,original_positive_inf_oppositeParabolic]

private theorem align_with_roots {G : Type*} [Group G]
    (U V : Subgroup G) (R : Fin 4→Subgroup G)
    (hperm : ∀F : MulAut G,U.map F.toMonoidHom=U→V.map F.toMonoidHom=V→
      ∃sigma : Equiv.Perm (Fin 4),∀a,(R a).map F.toMonoidHom=R (sigma a))
    (f : MulAut G) (halign : ∃g : G,U.map (MulAut.conj g*f).toMonoidHom=U ∧
      V.map (MulAut.conj g*f).toMonoidHom=V) :
    ∃(g : G) (sigma : Equiv.Perm (Fin 4)),
      U.map (MulAut.conj g*f).toMonoidHom=U ∧V.map (MulAut.conj g*f).toMonoidHom=V ∧
      ∀a,(R a).map (MulAut.conj g*f).toMonoidHom=R (sigma a) := by
  obtain ⟨g,hU,hV⟩ := halign
  obtain ⟨sigma,hsigma⟩ := hperm (MulAut.conj g*f) hU hV
  exact ⟨g,sigma,hU,hV,hsigma⟩

theorem exists_inner_fix_pair_and_root_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q)) :
    ∃(g : CFSG.Models.TwistedE6 q) (sigma : Equiv.Perm (Fin 4)),
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
        (MulAut.conj g*f).toMonoidHom=(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) ∧
      (originalNegative q).map (MulAut.conj g*f).toMonoidHom=originalNegative q ∧
      ∀a : Fin 4,(originalOrbitRoot q a).map (MulAut.conj g*f).toMonoidHom=
        originalOrbitRoot q (sigma a) :=
  align_with_roots (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))
    (originalNegative q) (originalOrbitRoot q) (exists_original_root_permutation q)
    f (original_exists_inner_fix_pair q f)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRootAction
