import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPolePairOperator
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddSingularSpanning
import SymmetricSubgroupAsymptotics.ScalarSpanMultiplicativeHomRange

/-! Every full odd-B pole shear is an actual elementary matrix word.
Singular parameters are literal long-root elements; the genuine additive
parameter hom and singular spanning extend membership to every parameter.
No linear-subspace property of the matrix subgroup is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShearElementary

open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBOddQuadraticForm CFSGOrthogonalBOddPoleCoordinates
open CFSGOrthogonalBOddPoleShear CFSGOrthogonalBOddPolePairOperator
open CFSGOrthogonalBIntrinsicLongRoots CFSGAlternatingPairOperator
variable (K : Type) [Field K] [Finite K]

def naturalLinearHom (n : ℕ) :
    elementaryRootGroup K n →* ((Index n → K) ≃ₗ[K] (Index n → K)) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index n → K))).toMonoidHom.comp
      (elementaryRootGroup K n).subtype

omit [Finite K] in
theorem naturalLinearHom_apply (n : ℕ) (g : elementaryRootGroup K n)
    (v : Index n → K) :
    naturalLinearHom K n g v = (g.val : Mat K n) *ᵥ v := rfl

theorem singular_poleShear_has_element (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Index (s + 2) → K) (hz : quadratic K (s + 2) z = 0) :
    ∃ g : elementaryRootGroup K (s + 3),
      naturalLinearHom K (s + 3) g = parameterHom K h2 (s + 2) (Multiplicative.ofAdd z) := by
  by_cases hz0 : z = 0
  · subst z
    refine ⟨1, ?_⟩
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact (poleShear_zero_apply K h2 (s + 2) v).symm
  let e : Index (s + 3) → K := Pi.single (pos (s + 3) 0) 1
  let w := tailExtension K (s + 2) z
  have he : e ≠ 0 := by
    intro h
    have hh := congrFun h (pos (s + 3) 0)
    simp [e] at hh
  have hee : (gram K (s + 3)).toBilin' e e = 0 := by
    rw [pairing_first_positive]
    simp [e, pos, neg]
  have hww : (gram K (s + 3)).toBilin' w w = 0 := by
    rw [tailExtension_norm]
    exact (quadratic_eq_zero_iff K h2 (s + 2) z).mp hz
  have hew : (gram K (s + 3)).toBilin' e w = 0 := by
    rw [pairing_first_positive]
    change 2 * tailExtension K (s + 2) z (neg (s + 3) 0) = 0
    rw [tailExtension_negative_head, mul_zero]
  have hnot : ∀ c : K, w ≠ c • e := by
    intro c hc
    have hh := congrArg (coordinateEquiv K h2 (s + 2)) hc
    change coordinates K (s + 2) (tailExtension K (s + 2) z) =
      coordinateEquiv K h2 (s + 2) (c • e) at hh
    rw [coordinates_tailExtension, map_smul] at hh
    change (0, (z, 0)) = c • coordinates K (s + 2) (Pi.single (pos (s + 3) 0) 1) at hh
    rw [coordinates_first] at hh
    have ht := congrArg (fun x : K × ((Index (s + 2) → K) × K) => x.2.1) hh
    exact hz0 (by simpa using ht)
  obtain ⟨g, _, hg, _, _⟩ := exists_longRoot_with_pairOperator h2 s e w he hee hww hew hnot (-1)
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [naturalLinearHom_apply, parameterHom_apply]
  change (g.val : Mat K (s + 3)) *ᵥ v = poleShear K h2 (s + 2) z v
  rw [poleShear_singular_pairOperator K h2 _ z hz]
  have hd := LinearMap.congr_fun hg v
  change ((g.val : Mat K (s + 3)) - 1) *ᵥ v =
    (-1 : K) • pairOperator (gram K (s + 3)).toBilin' e w v at hd
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, neg_one_smul] at hd
  calc
    (g.val : Mat K (s + 3)) *ᵥ v =
        ((g.val : Mat K (s + 3)) *ᵥ v - v) + v := (sub_add_cancel _ _).symm
    _ = -pairOperator (gram K (s + 3)).toBilin' e w v + v := congrArg (fun x => x + v) hd
    _ = _ := by change -pairOperator _ e w v + v = v - pairOperator _ e w v; abel

theorem parameterHom_mem_natural_range (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Index (s + 2) → K) :
    parameterHom K h2 (s + 2) (Multiplicative.ofAdd z) ∈
      (naturalLinearHom K (s + 3)).range := by
  apply ScalarSpanMultiplicativeHomRange.mem_of_span_eq_top (K := K)
    (parameterHom K h2 (s + 2)) (naturalLinearHom K (s + 3)).range
      {z : Index (s + 2) → K | quadratic K (s + 2) z = 0}
  · intro t ht a
    apply singular_poleShear_has_element K h2 s
    change quadratic K (s + 2) (a • t) = 0
    rw [QuadraticMap.map_smul, ht, smul_zero]
  · exact CFSGOrthogonalBOddSingularSpanning.singular_span_eq_top K h2 (s + 1)

theorem poleShear_has_element (h2 : (2 : K) ≠ 0) (s : ℕ)
    (z : Index (s + 2) → K) :
    ∃ g : elementaryRootGroup K (s + 3), ∀ v : Index (s + 3) → K,
      (g.val : Mat K (s + 3)) *ᵥ v = poleShear K h2 (s + 2) z v := by
  obtain ⟨g, hg⟩ := parameterHom_mem_natural_range K h2 s z
  refine ⟨g, ?_⟩
  intro v
  exact congrArg (fun A : (Index (s + 3) → K) ≃ₗ[K] (Index (s + 3) → K) => A v) hg

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddPoleShearElementary
