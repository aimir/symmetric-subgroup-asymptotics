import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarRankOneAction
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRootOrthogonality

/-! Every normalized rank-one coefficient in the actual two-plane shear
is an element of the original natural central root subgroup at its
literal singular point. The parameter is divided by the actual norm
of a chosen representative; no root-line identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists
open CFSGTwistedAUnitaryParameters

theorem starRankOne_eq_conjugate_of_scale (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) (g : naturalFixed (s + 3) q) (c b : q.Extension 2)
    (hb : Condition q (s + 1) 0 b)
    (hgv : unitaryCentralVector q s g = c • starVector q s v)
    (hscale : b * (c * definingFieldAutomorphism q 2 c) = t * a) :
    starFixed q s (starRankOneParameters q s t htc a ha v) =
      g * centralFixed q (s + 1) b hb * g⁻¹ := by
  apply unitaryNaturalEndHom_injective q (s + 3)
  rw [unitaryNaturalEndHom_central_root]
  apply LinearMap.ext
  intro x
  change ((starFixed q s (starRankOneParameters q s t htc a ha v)).val.val :
    Mat (q.Extension 2) (s + 3)) *ᵥ x =
      x + b • (centralRootAxisFunctional q s g x • unitaryCentralVector q s g)
  rw [starRankOne_action]
  have hp : centralRootAxisFunctional q s g x =
      definingFieldAutomorphism q 2 c * unitaryNaturalPair q (s + 3) (starVector q s v) x := by
    rw [← unitaryCentralVector_pair, hgv]
    exact (by simpa only [one_smul, mul_one] using
      (hermitianPair_smul (definingFieldAutomorphism q 2)
        (signedReversalUnit (q.Extension 2) (s + 3) : Mat (q.Extension 2) (s + 3))
        c 1 (starVector q s v) x))
  rw [hp, hgv, smul_smul, smul_smul]
  congr 1
  apply congrArg (fun z : q.Extension 2 => z • starVector q s v)
  calc
    (t * a) * unitaryNaturalPair q (s + 3) (starVector q s v) x =
      (b * (c * definingFieldAutomorphism q 2 c)) *
        unitaryNaturalPair q (s + 3) (starVector q s v) x := by rw [hscale]
    _ = (b * (definingFieldAutomorphism q 2 c *
        unitaryNaturalPair q (s + 3) (starVector q s v) x)) * c := by ring

theorem starRankOne_mem_conjugateRootLine (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
    (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a)
    (v : Fin 2 → q.Extension 2) (g : naturalFixed (s + 3) q) (c : q.Extension 2)
    (hc : c ≠ 0) (hgv : unitaryCentralVector q s g = c • starVector q s v) :
    starFixed q s (starRankOneParameters q s t htc a ha v) ∈
      conjugateNaturalCentralRootLine q (s + 1) g := by
  let n : q.Extension 2 := c * definingFieldAutomorphism q 2 c
  have hn : n ≠ 0 := mul_ne_zero hc ((map_ne_zero (definingFieldAutomorphism q 2)).mpr hc)
  have hnf : definingFieldAutomorphism q 2 n = n := by
    have hcc : definingFieldAutomorphism q 2 (definingFieldAutomorphism q 2 c) = c :=
      extension_two_pow_twice q c
    dsimp only [n]
    rw [map_mul, hcc]
    exact mul_comm _ _
  have haf : definingFieldAutomorphism q 2 (a / n) = a / n := by
    rw [map_div₀, ha, hnf]
  let b : q.Extension 2 := t * (a / n)
  have hbc : b ∈ centralParameters q (s + 1) :=
    star_central_mul_fixed q s t htc (a / n) haf
  have hb : Condition q (s + 1) 0 b := centralParameters_condition q (s + 1) b hbc
  have hscale : b * (c * definingFieldAutomorphism q 2 c) = t * a := by
    change (t * (a / n)) * n = t * a
    rw [mul_assoc, div_mul_cancel₀ a hn]
  rw [starRankOne_eq_conjugate_of_scale q s t htc a ha v g c b hb hgv hscale]
  exact ⟨centralFixed q (s + 1) b hb,
    (mem_naturalCentralRootLine_iff q (s + 1) _).mpr ⟨b, hb, rfl⟩, rfl⟩

theorem exists_starRankOne_root_representative (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) (hv : v ≠ 0) :
    ∃ (g : naturalFixed (s + 3) q) (c : q.Extension 2), c ≠ 0 ∧
      unitaryCentralVector q s g = c • starVector q s v ∧
      ∀ (t : q.Extension 2) (htc : t ∈ centralParameters q (s + 1))
        (a : q.Extension 2) (ha : definingFieldAutomorphism q 2 a = a),
        starFixed q s (starRankOneParameters q s t htc a ha v) ∈
          conjugateNaturalCentralRootLine q (s + 1) g := by
  obtain ⟨g, c, hc, hgv⟩ := exists_starVector_representative q s v hv
  exact ⟨g, c, hc, hgv, fun t htc a ha =>
    starRankOne_mem_conjugateRootLine q s t htc a ha v g c hc hgv⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
