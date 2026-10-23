import SymmetricSubgroupAsymptotics.CFSGTwistedA2HeisenbergCentralAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeDisjoint

/-! The rank-two Heisenberg centre survives the SAME original derived
centre quotient. The reversal belongs to that derived source by the
proved rank-two cover, and literal upper/opposite intersection is one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

theorem rankTwoOriginalDerived_central_upper_eq_one (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) (z : commutator (Fixed 2 q))
    (hz : z ∈ Subgroup.center (commutator (Fixed 2 q)))
    (hu : z.val ∈ originalUnipotent 2 q) : z = 1 := by
  let D := commutator (Fixed 2 q)
  let w : D := rankTwoDerivedCover q hq (reversalFixed q 2)
  have hc : w * z = z * w := Subgroup.mem_center_iff.mp hz w
  have hconj : w * z * w⁻¹ = z := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hw : w.val = originalReversal q 2 := rfl
  have hv : z.val ∈ originalOppositeUnipotent q 2 := by
    refine ⟨z.val, hu, ?_⟩
    have hh := congrArg (fun x : D => x.val) hconj
    change w.val * z.val * w.val⁻¹ = z.val at hh
    simpa only [hw] using hh
  have hh : z.val ∈ originalUnipotent 2 q ⊓ originalOppositeUnipotent q 2 := ⟨hu, hv⟩
  rw [original_upper_inf_opposite q 2 (by decide)] at hh
  exact Subtype.ext hh

theorem rankTwoCentralParameterHom_injective (q : CFSG.PrimePower)
    (hq : 3 ≤ q.order) : Function.Injective (rankTwoCentralParameterHom q hq) := by
  apply ((rankTwoCentralParameterHom q hq).ker_eq_bot_iff).mp
  apply bot_unique
  intro c hc
  change c = 1
  let z := rankTwoDerivedCover q hq (centralRadicalHom q 0 c).val
  have hz : z ∈ Subgroup.center (commutator (Fixed 2 q)) := by
    change QuotientGroup.mk' (Subgroup.center (commutator (Fixed 2 q))) z = 1 at hc
    exact (QuotientGroup.eq_one_iff _).mp hc
  have hu : z.val ∈ originalUnipotent 2 q := by
    refine ⟨radicalElement q 0 0 c.toAdd.val
      (centralParameters_condition q 0 c.toAdd.val c.toAdd.property), ?_⟩
    rfl
  have he := rankTwoOriginalDerived_central_upper_eq_one q hq z hz hu
  let u := radicalElement q 0 0 c.toAdd.val
    (centralParameters_condition q 0 c.toAdd.val c.toAdd.property)
  have hu0 : u = 1 := by
    apply unipotentToOriginalFixed_injective 2 (by decide) q
    change z.val = unipotentToOriginalFixed 2 q 1
    rw [map_one]
    exact congrArg (fun x : commutator (Fixed 2 q) => x.val) he
  have hm := congrArg (fun x : naturalUnipotent 2 q =>
    (x.val.val : Mat (q.Extension 2) 2) 0 (Fin.last 2)) hu0
  change ((radicalElement q 0 0 c.toAdd.val
    (centralParameters_condition q 0 c.toAdd.val c.toAdd.property)).val.val :
    Mat (q.Extension 2) 2) 0 (Fin.last 2) = (1 : Mat (q.Extension 2) 2) 0 (Fin.last 2) at hm
  rw [radicalCentral_matrix] at hm
  have hzero : c.toAdd.val = 0 := by
    simpa only [Matrix.add_apply, Matrix.one_apply, if_neg (by decide : (0 : Fin 3) ≠ Fin.last 2),
      Matrix.single_apply_same, zero_add] using hm
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hzero

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
