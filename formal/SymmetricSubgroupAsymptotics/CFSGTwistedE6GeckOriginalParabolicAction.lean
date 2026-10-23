import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! Automorphisms of the ORIGINAL twisted E6 group preserving its actual
positive Sylow permute the four literal minimal parabolics. Every
original automorphism admits an inner adjustment preserving the opposed
Sylow pair and carrying this permutation. No source lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParabolicAction
open CFSGTwistedE6GeckOriginalMinimalParabolics CFSGTwistedE6GeckOriginalUpperNormalizer
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalOppositeAlignment
open CFSGTwistedE6GeckOriginalPairAlignment CFSGMinimalOvergroupAutomorphismAction

private theorem align_with_family {G : Type*} [Group G]
    (U V : Subgroup G) (P : Fin 4→Subgroup G)
    (hperm : ∀F : MulAut G,U.map F.toMonoidHom=U→
      ∃sigma : Equiv.Perm (Fin 4),∀a,(P a).map F.toMonoidHom=P (sigma a))
    (f : MulAut G)
    (halign : ∃g : G,U.map (MulAut.conj g*f).toMonoidHom=U ∧
      V.map (MulAut.conj g*f).toMonoidHom=V) :
    ∃(g : G) (sigma : Equiv.Perm (Fin 4)),
      U.map (MulAut.conj g*f).toMonoidHom=U ∧
      V.map (MulAut.conj g*f).toMonoidHom=V ∧
      ∀a,(P a).map (MulAut.conj g*f).toMonoidHom=P (sigma a) := by
  obtain ⟨g,hU,hV⟩ := halign
  obtain ⟨sigma,hsigma⟩ := hperm (MulAut.conj g*f) hU
  exact ⟨g,sigma,hU,hV,hsigma⟩

theorem exists_original_parabolic_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (hU : (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map f.toMonoidHom=
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))) :
    ∃sigma : Equiv.Perm (Fin 4),∀a : Fin 4,
      (originalSimpleParabolic q a).map f.toMonoidHom=originalSimpleParabolic q (sigma a) := by
  have hB : (Subgroup.normalizer
      (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))).map f.toMonoidHom=
      Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q)) := by
    have hn := Subgroup.map_equiv_normalizer_eq
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) f
    have he := congrArg (fun P : Subgroup (CFSG.Models.TwistedE6 q)=>
      Subgroup.normalizer (P : Set (CFSG.Models.TwistedE6 q))) hU
    exact hn.trans he
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q)))
    (originalSimpleParabolic q) (original_upper_lt_simpleParabolic q)
    (original_simpleParabolic_minimal q) (original_minimal_overgroup_eq_simpleParabolic q)
    (originalSimpleParabolic_injective q) f hB

theorem exists_inner_fix_pair_and_parabolic_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q)) :
    ∃(g : CFSG.Models.TwistedE6 q) (sigma : Equiv.Perm (Fin 4)),
      (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)).map
        (MulAut.conj g*f).toMonoidHom=(originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q)) ∧
      (originalNegative q).map (MulAut.conj g*f).toMonoidHom=originalNegative q ∧
      ∀a : Fin 4,(originalSimpleParabolic q a).map (MulAut.conj g*f).toMonoidHom=
        originalSimpleParabolic q (sigma a) := by
  exact align_with_family (originalPositiveSylow q : Subgroup (CFSG.Models.TwistedE6 q))
    (originalNegative q) (originalSimpleParabolic q) (exists_original_parabolic_permutation q)
    f (original_exists_inner_fix_pair q f)

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalParabolicAction
