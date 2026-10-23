import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedCover
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLowerOpposite
import SymmetricSubgroupAsymptotics.CFSGDiagonalRegularCentralizer

/-! Natural lifts of the centre of the ORIGINAL derived fixed source
are scalar. Upper-normalizer rigidity gives one triangular direction;
the same argument after the literal reversal gives the other. Scalar
separation for actual p-elements makes central conjugation commute with
the checked regular upper matrix. No centre formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAIntervalSource

private theorem map_conjugate_of_central {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : G) (hg : f g ∈ Subgroup.center H) (w : G) :
    f (w * g * w⁻¹) = f g := by
  rw [map_mul, map_mul, map_inv, Subgroup.mem_center_iff.mp hg (f w),
    mul_assoc, mul_inv_cancel, mul_one]

theorem central_cover_commutes_upper (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q)
    (hg : originalDerivedCover q s g ∈ Subgroup.center
      (commutator (CFSGTwistedAUpperUnipotent.Fixed (s + 3) q)))
    (u : naturalUnipotent (s + 3) q) :
    (g.val.val : Mat (q.Extension 2) (s + 3)) * u.val.val =
      u.val.val * (g.val.val : Mat (q.Extension 2) (s + 3)) := by
  let D := commutator (CFSGTwistedAUpperUnipotent.Fixed (s + 3) q)
  let v : D := ⟨unipotentToOriginalFixed (s + 3) q u,
    originalUnipotent_le_derived q s ⟨u, rfl⟩⟩
  have hc : originalDerivedCover q s g * v * (originalDerivedCover q s g)⁻¹ = v := by
    have hh := Subgroup.mem_center_iff.mp hg v
    rw [← hh, mul_assoc, mul_inv_cancel, mul_one]
  have ha := congrArg (fun z : D => twistedFixedAction (s + 3) q z.val) hc
  have hga : twistedFixedAction (s + 3) q (originalDerivedCover q s g).val =
      naturalElementaryAction (q.Extension 2) (s + 3) g.val :=
    elementaryToModel_action (q.Extension 2) (s + 3) g.val
  change twistedFixedAction (s + 3) q
    ((originalDerivedCover q s g).val * unipotentToOriginalFixed (s + 3) q u *
      ((originalDerivedCover q s g).val)⁻¹) =
        twistedFixedAction (s + 3) q (unipotentToOriginalFixed (s + 3) q u) at ha
  simp only [map_mul, map_inv, unipotentToOriginalFixed_action, hga] at ha
  have he := upper_conjugate_of_action_eq q (s + 3) (by omega) g.val u u (by
    simpa only [map_mul, map_inv] using ha)
  have hh := congrArg (fun a : NaturalElementary (q.Extension 2) (s + 3) =>
    (a.val : Mat (q.Extension 2) (s + 3)) * (g.val.val : Mat (q.Extension 2) (s + 3))) he
  change (((g.val.val : Mat (q.Extension 2) (s + 3)) * u.val.val) *
      (↑(g.val.val⁻¹) : Mat (q.Extension 2) (s + 3))) * g.val.val = _ at hh
  simpa only [mul_assoc, Units.inv_mul, mul_one] using hh

theorem central_cover_scalar (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q)
    (hg : originalDerivedCover q s g ∈ Subgroup.center
      (commutator (CFSGTwistedAUpperUnipotent.Fixed (s + 3) q))) :
    ∃ c : q.Extension 2, (g.val.val : Mat (q.Extension 2) (s + 3)) = c • 1 := by
  have hu := central_cover_upper q s g hg
  let w := reversalFixed q (s + 3)
  have hc : originalDerivedCover q s (w * g * w⁻¹) = originalDerivedCover q s g :=
    map_conjugate_of_central (originalDerivedCover q s) g hg w
  have hr := central_cover_upper q s (w * g * w⁻¹) (hc.symm ▸ hg)
  have hoff (i j : Fin (s + 4)) (hij : i ≠ j) :
      (g.val.val : Mat (q.Extension 2) (s + 3)) i j = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hz := hr (Fin.rev_lt_rev.mpr hlt)
      change ((signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3)) *
        (g.val.val : Mat (q.Extension 2) (s + 3)) *
          (↑((signedReversalUnit (q.Extension 2) (s + 3))⁻¹) : Mat (q.Extension 2) (s + 3)))
            i.rev j.rev = 0 at hz
      rw [signedReversal_conjugation_entry, Fin.rev_rev, Fin.rev_rev] at hz
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right
        (signWeight_ne_zero (q.Extension 2) (s + 3) j.rev))).resolve_left
          (signWeight_ne_zero (q.Extension 2) (s + 3) i.rev)
    · exact hu hgt
  obtain ⟨u, hregular⟩ := exists_regular_upper q (s + 3)
  exact CFSGDiagonalRegularCentralizer.scalar_of_diagonal_regular
    (g.val.val : Mat (q.Extension 2) (s + 3)) u.val.val hoff hregular
      (central_cover_commutes_upper q s g hg u)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
