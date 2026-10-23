import SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacencyNecessity
import SymmetricSubgroupAsymptotics.CFSGTwistedDAdjacentRootProducts

/-! Exact intrinsic root-product adjacency on the actual central
quotient, with the actual fixed-field quadratic Grassmann planes.
Specific root elements remain injective through the central quotient;
no quotient-automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacency
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDPlaneRootLine CFSGTwistedDSingularPlaneOrbit CFSGTwistedDRootPlaneImage
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDProjectiveRootFamily
open CFSGTwistedDProjectivePlaneLabel CFSGTwistedDIntrinsicRootProduct
open CFSGTwistedDAdjacentRootProducts CFSGTwistedDRootProductAdjacencyNecessity
open CFSGTwistedA2FixedField

theorem root_eq_one_of_projective_eq_one (s : ℕ) (q : CFSG.PrimePower)
    (x : relativeRootGroup (s + 2) q) (hx : IsRootElement s q x)
    (he : projection s q x = 1) : x = 1 := by
  obtain ⟨g, a, rfl⟩ := hx
  have hh : projection s q (g * highestRoot s q a * g⁻¹) =
      projection s q (1 * highestRoot s q 0 * (1 : relativeRootGroup (s + 2) q)⁻¹) := by
    simpa only [highestRoot_zero s q, mul_one, one_mul, inv_one, map_one] using he
  have hu := conjugate_highest_eq_of_projective_eq s q g 1 a 0 hh
  simpa only [highestRoot_zero s q, mul_one, one_mul, inv_one] using hu

theorem projective_root_product_adjacency_iff (s : ℕ) (q : CFSG.PrimePower)
    (g h : relativeRootGroup (s + 2) q)
    (hne : conjugateRootPlane s q g ≠ conjugateRootPlane s q h) :
    RootProductRelation s q
      (projectiveConjugateRootLine s q (projection s q g))
      (projectiveConjugateRootLine s q (projection s q h)) ↔
      (Module.finrank (fixedField q)
        (conjugateRootPlane s q g ⊓ conjugateRootPlane s q h :
          Submodule (fixedField q) (fixedSpace (s + 2) q)) = 1 ∧
        ∀ z ∈ conjugateRootPlane s q g ⊔ conjugateRootPlane s q h,
          fixedQuadraticForm (s + 2) q z = 0) := by
  constructor
  · exact root_product_forces_adjacency s q g h hne
  · rintro ⟨hdim, hs⟩
    have hmeet : (conjugateRootPlane s q g ⊓ conjugateRootPlane s q h :
        Submodule (fixedField q) (fixedSpace (s + 2) q)) ≠ ⊥ := by
      intro he
      have hz := congrArg
        (fun T : Submodule (fixedField q) (fixedSpace (s + 2) q) =>
          Module.finrank (fixedField q) T) he
      dsimp only at hz
      rw [finrank_bot, hdim] at hz
      omega
    obtain ⟨x, hx, hxn, y, hy, hyn, hc, hp⟩ :=
      adjacent_planes_have_root_product s q g h hne hmeet hs
    have hru : IsRootElement s q x := by
      obtain ⟨a, ha⟩ := (mem_conjugateRootLine_iff s q g x).mp hx
      exact ⟨g, a, ha⟩
    have hrv : IsRootElement s q y := by
      obtain ⟨b, hb⟩ := (mem_conjugateRootLine_iff s q h y).mp hy
      exact ⟨h, b, hb⟩
    refine ⟨projection s q x, ?_, ?_, projection s q y, ?_, ?_, ?_, ?_⟩
    · rw [← map_conjugateRootLine]
      exact ⟨x, hx, rfl⟩
    · exact fun he => hxn (root_eq_one_of_projective_eq_one s q x hru he)
    · rw [← map_conjugateRootLine]
      exact ⟨y, hy, rfl⟩
    · exact fun he => hyn (root_eq_one_of_projective_eq_one s q y hrv he)
    · change projection s q x * projection s q y = projection s q y * projection s q x
      rw [← map_mul, ← map_mul, hc.eq]
    · exact ⟨x * y, hp, (projection s q).map_mul x y⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedDRootProductAdjacency
