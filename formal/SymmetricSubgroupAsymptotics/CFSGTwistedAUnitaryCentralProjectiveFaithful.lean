import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCentralNormOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOppositeDisjoint

/-! The actual central parameter line survives the ACTUAL original
derived-centre quotient. A derived-central element in original U lies
also in its literal opposite, whose intersection has already been proved
trivial. No scalar commutant or centre-order hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

theorem originalDerived_central_upper_eq_one (q : CFSG.PrimePower) (s : ℕ)
    (z : commutator (Fixed (s + 3) q))
    (hz : z ∈ Subgroup.center (commutator (Fixed (s + 3) q)))
    (hu : z.val ∈ originalUnipotent (s + 3) q) : z = 1 := by
  let D := commutator (Fixed (s + 3) q)
  let w : D := ⟨originalReversal q (s + 3), originalReversal_mem_derived q s⟩
  have hc : w * z = z * w := Subgroup.mem_center_iff.mp hz w
  have hconj : w * z * w⁻¹ = z := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  have hv : z.val ∈ originalOppositeUnipotent q (s + 3) :=
    ⟨z.val, hu, congrArg (fun x : D => x.val) hconj⟩
  have hh : z.val ∈ originalUnipotent (s + 3) q ⊓ originalOppositeUnipotent q (s + 3) :=
    ⟨hu, hv⟩
  rw [original_upper_inf_opposite q (s + 3) (by omega)] at hh
  exact Subtype.ext hh

theorem projectiveCentralParameterHom_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (projectiveCentralParameterHom q s) := by
  apply ((projectiveCentralParameterHom q s).ker_eq_bot_iff).mp
  apply bot_unique
  intro c hc
  change c = 1
  have hz : derivedCentralParameterHom q s c ∈
      Subgroup.center (commutator (Fixed (s + 3) q)) := by
    change QuotientGroup.mk' (Subgroup.center (commutator (Fixed (s + 3) q)))
      (derivedCentralParameterHom q s c) = 1 at hc
    exact (QuotientGroup.eq_one_iff _).mp hc
  have hu : (derivedCentralParameterHom q s c).val ∈ originalUnipotent (s + 3) q := by
    refine ⟨radicalElement q (s + 1) 0 c.toAdd.val
      (centralParameters_condition q (s + 1) c.toAdd.val c.toAdd.property), ?_⟩
    rfl
  have he := originalDerived_central_upper_eq_one q s (derivedCentralParameterHom q s c) hz hu
  let u := radicalElement q (s + 1) 0 c.toAdd.val
    (centralParameters_condition q (s + 1) c.toAdd.val c.toAdd.property)
  have hu0 : u = 1 := by
    apply unipotentToOriginalFixed_injective (s + 3) (by omega) q
    change (derivedCentralParameterHom q s c).val = unipotentToOriginalFixed (s + 3) q 1
    rw [map_one]
    exact congrArg (fun x : commutator (Fixed (s + 3) q) => x.val) he
  have hm := congrArg (fun x : naturalUnipotent (s + 3) q =>
    (x.val.val : Mat (q.Extension 2) (s + 3)) 0 (Fin.last (s + 3))) hu0
  change ((radicalElement q (s + 1) 0 c.toAdd.val
    (centralParameters_condition q (s + 1) c.toAdd.val c.toAdd.property)).val.val :
      Mat (q.Extension 2) (s + 3)) 0 (Fin.last (s + 3)) =
        (1 : Mat (q.Extension 2) (s + 3)) 0 (Fin.last (s + 3)) at hm
  rw [radicalCentral_matrix] at hm
  have hn : (0 : Fin (s + 4)) ≠ Fin.last (s + 3) := by
    intro heq
    have hv := congrArg (fun i : Fin (s + 4) => i.val) heq
    change 0 = s + 3 at hv
    omega
  have hzero : c.toAdd.val = 0 := by
    simpa only [Matrix.add_apply, Matrix.one_apply, if_neg hn, Matrix.single_apply_same,
      zero_add] using hm
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hzero

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
