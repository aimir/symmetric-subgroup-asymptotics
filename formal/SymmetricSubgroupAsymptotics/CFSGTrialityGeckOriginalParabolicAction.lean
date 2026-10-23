import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalMinimalParabolics
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! Automorphisms of the ORIGINAL triality D4 group preserving its actual
positive Sylow permute the two literal minimal parabolics. Every
original automorphism admits an inner adjustment preserving the opposed
Sylow pair and carrying this permutation. No source lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParabolicAction
open CFSGTrialityGeckOriginalMinimalParabolics CFSGTrialityGeckOriginalUpperNormalizer
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckOriginalPairAlignment CFSGMinimalOvergroupAutomorphismAction

private theorem align_with_family {G : Type*} [Group G]
    (U V : Subgroup G) (P : Bool→Subgroup G)
    (hperm : ∀F : MulAut G,U.map F.toMonoidHom=U→
      ∃sigma : Equiv.Perm (Bool),∀a,(P a).map F.toMonoidHom=P (sigma a))
    (f : MulAut G)
    (halign : ∃g : G,U.map (MulAut.conj g*f).toMonoidHom=U ∧
      V.map (MulAut.conj g*f).toMonoidHom=V) :
    ∃(g : G) (sigma : Equiv.Perm (Bool)),
      U.map (MulAut.conj g*f).toMonoidHom=U ∧
      V.map (MulAut.conj g*f).toMonoidHom=V ∧
      ∀a,(P a).map (MulAut.conj g*f).toMonoidHom=P (sigma a) := by
  obtain ⟨g,hU,hV⟩ := halign
  obtain ⟨sigma,hsigma⟩ := hperm (MulAut.conj g*f) hU
  exact ⟨g,sigma,hU,hV,hsigma⟩

theorem exists_original_parabolic_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hU : (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map f.toMonoidHom=
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))) :
    ∃sigma : Equiv.Perm (Bool),∀a : Bool,
      (originalSimpleParabolic q a).map f.toMonoidHom=originalSimpleParabolic q (sigma a) := by
  have hB : (Subgroup.normalizer
      (originalSylow q : Set (CFSG.Models.TrialityD4 q))).map f.toMonoidHom=
      Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q)) := by
    have hn := Subgroup.map_equiv_normalizer_eq
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) f
    have he := congrArg (fun P : Subgroup (CFSG.Models.TrialityD4 q)=>
      Subgroup.normalizer (P : Set (CFSG.Models.TrialityD4 q))) hU
    exact hn.trans he
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q)))
    (originalSimpleParabolic q) (original_upper_lt_simpleParabolic q)
    (original_simpleParabolic_minimal q) (original_minimal_overgroup_eq_simpleParabolic q)
    (originalSimpleParabolic_injective q) f hB

theorem exists_inner_fix_pair_and_parabolic_permutation (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q)) :
    ∃(g : CFSG.Models.TrialityD4 q) (sigma : Equiv.Perm (Bool)),
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map
        (MulAut.conj g*f).toMonoidHom=(originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) ∧
      (originalNegative q).map (MulAut.conj g*f).toMonoidHom=originalNegative q ∧
      ∀a : Bool,(originalSimpleParabolic q a).map (MulAut.conj g*f).toMonoidHom=
        originalSimpleParabolic q (sigma a) := by
  exact align_with_family (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))
    (originalNegative q) (originalSimpleParabolic q) (exists_original_parabolic_permutation q)
    f (original_exists_inner_fix_pair q f)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalParabolicAction
