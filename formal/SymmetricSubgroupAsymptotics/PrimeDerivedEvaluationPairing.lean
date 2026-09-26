import SymmetricSubgroupAsymptotics.PrimeDerivedCommutatorPairing
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.BilinearMap

/-! Transport the original derived-character pairing to the canonical
prime evaluation space when its actual kernel is G'. The coordinate
vectors are evaluations of the original elements. No chosen finite model,
independence assertion, or group-order premise is needed for this transport.
-/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G]

/-- The exact kernel identity identifies the actual two quotient maps. -/
def derivedAbelianizationEquiv
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G) :
    Abelianization G ≃* Multiplicative (PrimeAbelianization p G) :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (primeAbelianizationGroupMap p G)
      (primeAbelianizationGroupMap_surjective p G))

@[simp] theorem derivedAbelianizationEquiv_of
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G) (g : G) :
    derivedAbelianizationEquiv p hker (Abelianization.of g) =
      primeAbelianizationGroupMap p G g := rfl

def derivedAbelianizationAddEquiv
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G) :
    Additive (Abelianization G) ≃+ PrimeAbelianization p G :=
  (derivedAbelianizationEquiv p hker).toAdditive

/-- Bilinear form on the canonical evaluation space, obtained from the
same actual commutator character under the quotient equivalence. -/
def derivedEvaluationBilinear
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (χ : primeRelativeCharacters p (commutator G)) :
    PrimeAbelianization p G →ₗ[ZMod p] PrimeAbelianization p G →ₗ[ZMod p] ZMod p := by
  letI := (derivedAbelianizationAddEquiv p hker).module (ZMod p)
  let e := (derivedAbelianizationAddEquiv p hker).linearEquiv (ZMod p)
  exact (derivedCharacterBilinear p χ).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap

/-- Original generators can be used directly as the matrix-coordinate
vectors; this identity is independent of any basis or rank certificate. -/
@[simp] theorem derivedEvaluationBilinear_eval
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (χ : primeRelativeCharacters p (commutator G)) (a b : G) :
    derivedEvaluationBilinear p hker χ
      (primeAbelianizationMap p G (Additive.ofMul a))
      (primeAbelianizationMap p G (Additive.ofMul b)) =
        derivedCharacterCommutator p χ a b := by
  letI := (derivedAbelianizationAddEquiv p hker).module (ZMod p)
  let e := (derivedAbelianizationAddEquiv p hker).linearEquiv (ZMod p)
  have he (g : G) : e (Additive.ofMul (Abelianization.of g)) =
      primeAbelianizationMap p G (Additive.ofMul g) := rfl
  change derivedCharacterBilinear p χ (e.symm _) (e.symm _) = _
  rw [← he a, ← he b, e.symm_apply_apply, e.symm_apply_apply]
  rfl

def derivedEvaluationBilinearMap
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G) :
    primeRelativeCharacters p (commutator G) →ₗ[ZMod p]
      PrimeAbelianization p G →ₗ[ZMod p] PrimeAbelianization p G →ₗ[ZMod p] ZMod p where
  toFun := derivedEvaluationBilinear p hker
  map_add' χ ψ := by
    ext v w
    obtain ⟨a, rfl⟩ := primeAbelianizationMap_surjective p G v
    obtain ⟨b, rfl⟩ := primeAbelianizationMap_surjective p G w
    simp only [LinearMap.add_apply]
    rfl
  map_smul' c χ := by
    ext v w
    obtain ⟨a, rfl⟩ := primeAbelianizationMap_surjective p G v
    obtain ⟨b, rfl⟩ := primeAbelianizationMap_surjective p G w
    simp only [LinearMap.smul_apply]
    rfl

theorem derivedEvaluationBilinear_self
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (χ : primeRelativeCharacters p (commutator G)) (v : PrimeAbelianization p G) :
    derivedEvaluationBilinear p hker χ v v = 0 := by
  obtain ⟨a, rfl⟩ := primeAbelianizationMap_surjective p G v
  exact (derivedEvaluationBilinear_eval p hker χ a.toMul a.toMul).trans
    (derivedCharacterCommutator_self p χ a.toMul)

/-- The actual image of N in the canonical prime evaluation space. -/
def primeDerivedImage (N : Subgroup G) : Submodule (ZMod p) (PrimeAbelianization p G) :=
  ((primeAbelianizationMap p G).comp N.subtype.toAdditive).range.toZModSubmodule p

theorem mem_primeDerivedImage_iff (N : Subgroup G) (v : PrimeAbelianization p G) :
    v ∈ primeDerivedImage p N ↔
      ∃ n : N, primeAbelianizationMap p G (Additive.ofMul (n : G)) = v := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.toMul, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨Additive.ofMul n, hn⟩

/-- Retained characters annihilate the entire actual image W, not merely
the selected original generator rows used in a finite matrix certificate. -/
theorem retained_derivedEvaluationBilinear_eq_zero
    (hker : (primeAbelianizationGroupMap p G).ker = commutator G)
    (N : Subgroup G) [N.Normal] (hDN : commutator G ≤ N)
    (χ : primeRelativeCharacters p (commutator G))
    (hχ : χ ∈ normalChainRetainedCharacters (commutator G) N p hDN)
    (v : PrimeAbelianization p G) (hv : v ∈ primeDerivedImage p N)
    (w : PrimeAbelianization p G) : derivedEvaluationBilinear p hker χ v w = 0 := by
  obtain ⟨n, rfl⟩ := (mem_primeDerivedImage_iff p N v).mp hv
  obtain ⟨g, rfl⟩ := primeAbelianizationMap_surjective p G w
  exact (derivedEvaluationBilinear_eval p hker χ (n : G) g.toMul).trans
    (normalChainRetainedCharacters_le_mixedAnnihilator
      (commutator G) N p hDN (Subgroup.commutator_mono le_top le_rfl) hχ n g.toMul)

end SymmetricSubgroupAsymptotics
