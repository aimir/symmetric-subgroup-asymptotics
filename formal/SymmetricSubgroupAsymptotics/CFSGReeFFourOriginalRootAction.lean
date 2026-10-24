import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootIntersections
import SymmetricSubgroupAsymptotics.CFSGMinimalOvergroupAutomorphismAction

/-! The q and q² root blocks are intrinsic in the SAME original Ree
quotient. Pair-preserving automorphisms permute the opposite minimal
family, and the distinct intersection cardinalities force both labels
to be fixed. No original automorphism lifts to the fixed Model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootAction
open CFSGReeFFourOriginalPositiveSylow CFSGReeFFourOriginalOppositeAlignment
open CFSGReeFFourOriginalPairAlignment CFSGReeFFourOriginalMinimalParabolics
open CFSGReeFFourOriginalRootIntersections CFSGMinimalOvergroupAutomorphismAction

theorem exists_original_opposite_parabolic_permutation (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) :
    ∃sigma : Equiv.Perm Bool,∀b : Bool,
      (originalNegativeSimpleParabolic m hm b).map f.toMonoidHom=
        originalNegativeSimpleParabolic m hm (sigma b) := by
  have hB : (Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m))).map
      f.toMonoidHom=Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m)) :=
    (Subgroup.map_equiv_normalizer_eq (originalNegative m hm) f).trans
      (congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Subgroup.normalizer
        (P : Set (CFSG.Models.ReeF4 m))) hV)
  exact exists_minimal_overgroup_permutation
    (Subgroup.normalizer (originalNegative m hm : Set (CFSG.Models.ReeF4 m)))
    (originalNegativeSimpleParabolic m hm) (original_negative_normalizer_lt_simpleParabolic m hm)
    (original_negativeSimpleParabolic_minimal m hm)
    (minimal_original_overgroup_eq_negativeSimpleParabolic m hm)
    (originalNegativeSimpleParabolic_injective m hm) f hB

theorem exists_original_root_permutation (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hU : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) :
    ∃sigma : Equiv.Perm Bool,∀b : Bool,
      (originalRootBlock m hm b).map f.toMonoidHom=originalRootBlock m hm (sigma b) := by
  obtain ⟨sigma,hsigma⟩ := exists_original_opposite_parabolic_permutation m hm f hV
  refine ⟨sigma,fun b=>?_⟩
  rw [←original_positive_inf_negativeSimpleParabolic,
    Subgroup.map_inf _ _ _ f.injective,hU,hsigma b,original_positive_inf_negativeSimpleParabolic]

theorem originalRootBlock_card_injective (m : ℕ) (hm : 0<m) :
    Function.Injective (fun b : Bool=>Nat.card (originalRootBlock m hm b)) := by
  intro b c he
  cases b <;> cases c <;> try rfl
  all_goals
    exfalso
    dsimp only at he
    rw [originalRootBlock_card,originalRootBlock_card] at he
    simp only [Bool.false_eq_true,ite_false,ite_true,pow_one,pow_two] at he
    have hq : 2≤2^(2*m+1) :=
      (by decide : 2≤(2 : ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
    nlinarith

theorem original_root_block_map_eq (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m))
    (hU : (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))
    (hV : (originalNegative m hm).map f.toMonoidHom=originalNegative m hm) (b : Bool) :
    (originalRootBlock m hm b).map f.toMonoidHom=originalRootBlock m hm b := by
  obtain ⟨sigma,hsigma⟩ := exists_original_root_permutation m hm f hU hV
  have hc := Nat.card_congr (f.subgroupMap (originalRootBlock m hm b)).toEquiv
  change Nat.card (originalRootBlock m hm b)=
    Nat.card ((originalRootBlock m hm b).map f.toMonoidHom) at hc
  have he : b=sigma b := originalRootBlock_card_injective m hm
    (hc.trans (congrArg (fun P : Subgroup (CFSG.Models.ReeF4 m)=>Nat.card P) (hsigma b)))
  have hh := hsigma b
  rw [←he] at hh
  exact hh

theorem exists_inner_fix_pair_and_root_blocks (m : ℕ) (hm : 0<m)
    (f : MulAut (CFSG.Models.ReeF4 m)) :
    ∃g : CFSG.Models.ReeF4 m,
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map (MulAut.conj g*f).toMonoidHom=
        (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) ∧
      (originalNegative m hm).map (MulAut.conj g*f).toMonoidHom=originalNegative m hm ∧
      ∀b : Bool,(originalRootBlock m hm b).map (MulAut.conj g*f).toMonoidHom=
        originalRootBlock m hm b := by
  obtain ⟨g,hU,hV⟩ := original_exists_inner_fix_pair m hm f
  exact ⟨g,hU,hV,original_root_block_map_eq m hm (MulAut.conj g*f) hU hV⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootAction
