import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoCentralUpper
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixTriangularUnits
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeDisjoint

/-! The actual triangular flag subgroup, its opposite upper group, and
the central-kernel containment needed to count their quotient images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def rankTwoUpperFlag (q : CFSG.PrimePower) : Subgroup (naturalFixed 2 q) :=
  (CFSGGradedMatrixTriangularUnits.triangularUnits
    (K := q.Extension 2) (fun i : Fin 3 => (i.val : ℤ))).comap (fixedMatrixHom q 2)

theorem rankTwoUpperFlag_mem_iff (q : CFSG.PrimePower) (g : naturalFixed 2 q) :
    g ∈ rankTwoUpperFlag q ↔ (g.val.val : Mat (q.Extension 2) 2).BlockTriangular id := by
  constructor
  · intro h i j hij
    exact h (show (j.val : ℤ) < i.val by exact_mod_cast hij)
  · intro h i j hij
    change (j.val : ℤ) < (i.val : ℤ) at hij
    have hn : j.val < i.val := by exact_mod_cast hij
    exact h hn

def rankTwoUpperSubgroup (q : CFSG.PrimePower) : Subgroup (naturalFixed 2 q) :=
  (naturalUnipotent 2 q).subgroupOf (naturalFixed 2 q)

def rankTwoOppositeSubgroup (q : CFSG.PrimePower) : Subgroup (naturalFixed 2 q) :=
  (rankTwoUpperSubgroup q).map (MulAut.conj (reversalFixed q 2)).toMonoidHom

theorem rankTwoUpperSubgroup_le_flag (q : CFSG.PrimePower) :
    rankTwoUpperSubgroup q ≤ rankTwoUpperFlag q := by
  intro g hg
  exact (rankTwoUpperFlag_mem_iff q g).mpr hg.1.1

theorem rankTwoProjectiveCover_kernel_le_flag (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    (rankTwoProjectiveCover q hq).ker ≤ rankTwoUpperFlag q := by
  intro g hg
  exact (rankTwoUpperFlag_mem_iff q g).mpr (rankTwo_central_cover_upper q hq g
    ((QuotientGroup.eq_one_iff _).mp hg))

theorem rankTwoOpposite_inf_flag (q : CFSG.PrimePower) :
    rankTwoOppositeSubgroup q ⊓ rankTwoUpperFlag q = ⊥ := by
  apply bot_unique
  rintro g ⟨hg, hb⟩
  obtain ⟨u, hu, he⟩ := hg
  have hm : g.val ∈ oppositeNaturalUnipotent q 2 :=
    ⟨u.val, hu, congrArg Subtype.val he⟩
  have hdiag (i : Fin 3) : (g.val.val : Mat (q.Extension 2) 2) i i = 1 := by
    have hi := congrArg (fun x : naturalFixed 2 q =>
      (x.val.val : Mat (q.Extension 2) 2) i i) he
    change ((signedReversalUnit (q.Extension 2) 2 : Mat (q.Extension 2) 2) *
      (u.val.val : Mat (q.Extension 2) 2) *
      (↑((signedReversalUnit (q.Extension 2) 2)⁻¹) : Mat (q.Extension 2) 2)) i i = _ at hi
    have hd : (u.val.val : Mat (q.Extension 2) 2) i.rev i.rev = 1 := hu.1.2 i.rev
    rw [signedReversal_conjugation_entry, hd, mul_one] at hi
    have hs : signWeight (q.Extension 2) 2 i * signWeight (q.Extension 2) 2 i = 1 := by
      change ((-1 : q.Extension 2) ^ i.val) * ((-1 : q.Extension 2) ^ i.val) = 1
      rw [← mul_pow]
      simp
    exact hi.symm.trans hs
  let v : naturalUnipotent 2 q :=
    ⟨g.val, ⟨(rankTwoUpperFlag_mem_iff q g).mp hb, hdiag⟩, g.property⟩
  have hv := upper_eq_one_of_mem_opposite q 2 v hm
  change g = 1
  exact Subtype.ext (congrArg (fun x : naturalUnipotent 2 q => x.val) hv)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
