import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarSemilinearVectors
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOneRays

/-! The original automorphism action on every point of the canonical
singular two-plane is induced by an actual extension-field semilinear
injection. The final identification uses the exact original root-line
labels and a nonzero rank-one coefficient, preserving the same point
carrier throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGHermitianTwoByTwoRankOne

theorem exists_unitaryStar_point_semilinear (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∃ theta : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) theta ∧
      ∃ L : (Fin 2 → q.Extension 2) →ₛₗ[theta.toRingHom] (Fin 2 → q.Extension 2),
        Function.Injective L ∧ ∀ (v : Fin 2 → q.Extension 2) (hv : v ≠ 0),
          (unitarySingularPointActionHom q s f (starPoint q s v hv)).val =
            (q.Extension 2) ∙ starVector q s (L v) := by
  obtain ⟨theta, htheta, L, hL, c, hc, hc0, hR⟩ :=
    exists_unitaryStar_semilinear_vectors q s t ht htc f hinc
  refine ⟨theta, htheta, L, hL, ?_⟩
  intro v hv
  have hLv : L v ≠ 0 := by
    intro h
    apply hv
    apply hL
    exact h.trans (map_zero L).symm
  have hQ : (unitarySingularPointActionHom q s f (starPoint q s v hv)).val ≤ starPlane q s :=
    (hinc (starPoint q s v hv)).mpr (starPoint_le_starPlane q s v hv)
  obtain ⟨w, hw, hew⟩ := exists_starPoint_of_le q s
    (unitarySingularPointActionHom q s f (starPoint q s v hv)) hQ
  have hline := unitaryStarCoefficientAut_rootLine q s t ht htc f hinc v w hv hw hew.symm
  have hmem : unitaryStarCoefficientAut q s t ht htc f hinc
      (rankOneParameter (definingFieldAutomorphism q 2)
        (fun z => extension_two_pow_twice q z) 1 (map_one _) v) ∈
      rankOneLine (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) w := by
    rw [← hline]
    exact ⟨rankOneParameter (definingFieldAutomorphism q 2)
      (fun z => extension_two_pow_twice q z) 1 (map_one _) v, ⟨1, map_one _, rfl⟩, rfl⟩
  rw [hR v] at hmem
  have hspan := span_eq_of_nonzero_rankOne_mem_line (definingFieldAutomorphism q 2)
    (fun z => extension_two_pow_twice q z) c hc hc0 (L v) w hLv hw hmem
  have hmap := congrArg (fun S : Submodule (q.Extension 2) (Fin 2 → q.Extension 2) =>
    S.map (starVectorLinear q s)) hspan
  dsimp only at hmap
  rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton] at hmap
  change (q.Extension 2) ∙ starVector q s (L v) = (q.Extension 2) ∙ starVector q s w at hmap
  rw [← hew]
  exact hmap.symm

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
