import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOuterWeyl
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryNaturalColumnClearing

/-! Actual upper/opposite words send the first column of EVERY defining-
fixed matrix to a nonzero multiple of the first basis vector. The word
uses the proved opposite pivot, actual radical clearing, and the literal
three-root outer Weyl word. No transitivity or generation hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical

theorem exists_join_first_column_axis (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 2) q) :
    ∃ h : naturalFixed (s + 2) q,
      h.val ∈ naturalUpperOppositeJoin q (s + 2) ∧
      ∃ a : q.Extension 2, a ≠ 0 ∧
        (fun i => ((h * g).val.val : Mat (q.Extension 2) (s + 2)) i 0) = Pi.single 0 a := by
  obtain ⟨v, hv, hb⟩ := exists_opposite_first_column_pivot q s g
  let G := v * g
  let b : q.Extension 2 := (G.val.val : Mat (q.Extension 2) (s + 2)) (Fin.last (s + 2)) 0
  obtain ⟨u, hu⟩ := upper_clear_natural_column q s G hb
  obtain ⟨t, ht0, ht⟩ := exists_nonzero_central_parameter q s
  let U : naturalFixed (s + 2) q := ⟨u.val, u.property.2⟩
  let W := outerWeylFixed q s t ht
  let h := W * U * v
  have hU : naturalUnipotent (s + 2) q ≤ naturalUpperOppositeJoin q (s + 2) := le_sup_left
  have hO : oppositeNaturalUnipotent q (s + 2) ≤ naturalUpperOppositeJoin q (s + 2) := le_sup_right
  have hh : h.val ∈ naturalUpperOppositeJoin q (s + 2) :=
    (naturalUpperOppositeJoin q (s + 2)).mul_mem
      ((naturalUpperOppositeJoin q (s + 2)).mul_mem
        (outerWeyl_mem_join q s t ht) (hU u.property)) (hO hv)
  refine ⟨h, hh, t * b, mul_ne_zero ht0 hb, ?_⟩
  have hact : (fun i => ((h * g).val.val : Mat (q.Extension 2) (s + 2)) i 0) =
      (W.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ
        (fun i => ((U * G).val.val : Mat (q.Extension 2) (s + 2)) i 0) := by
    funext i
    change ((((W.val.val : Mat (q.Extension 2) (s + 2)) *
        (u.val.val : Mat (q.Extension 2) (s + 2))) *
        (v.val.val : Mat (q.Extension 2) (s + 2))) *
        (g.val.val : Mat (q.Extension 2) (s + 2))) i 0 =
      ((W.val.val : Mat (q.Extension 2) (s + 2)) *
        ((u.val.val : Mat (q.Extension 2) (s + 2)) *
          ((v.val.val : Mat (q.Extension 2) (s + 2)) *
            (g.val.val : Mat (q.Extension 2) (s + 2))))) i 0
    simp only [mul_assoc]
  rw [hact]
  have hu' : (fun i => ((U * G).val.val : Mat (q.Extension 2) (s + 2)) i 0) =
      Pi.single (Fin.last (s + 2)) b := hu
  rw [hu']
  exact outerWeyl_last_action q s t ht ht0 b

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
