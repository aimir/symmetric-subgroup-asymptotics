import SymmetricSubgroupAsymptotics.CFSGTwistedDAnisotropicNormForm
import SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeSpaceCoordinates

/-! Exact positive, negative and anisotropic projections of the SAME
fixed quadratic space, with quadratic and polar formulas. These retain
the actual extension coordinate and norm form in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates
open CFSGTwistedDLinearParameters CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedDMaximalSingularDimension CFSGTwistedDNegativeSpaceCoordinates
open CFSGTwistedDAnisotropicNormForm CFSGTwistedA2FixedField

def positivePart (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q →ₗ[fixedField q] (Fin (n + 1) → fixedField q) :=
  (LinearMap.fst (fixedField q) (Fin (n + 1) → fixedField q)
    ((Fin (n + 1) → fixedField q) × q.Extension 2)).comp (linearParameters n q).toLinearMap

def negativePart (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q →ₗ[fixedField q] (Fin (n + 1) → fixedField q) :=
  (LinearMap.fst (fixedField q) (Fin (n + 1) → fixedField q) (q.Extension 2)).comp
    ((LinearMap.snd (fixedField q) (Fin (n + 1) → fixedField q)
      ((Fin (n + 1) → fixedField q) × q.Extension 2)).comp (linearParameters n q).toLinearMap)

def anisotropicPart (n : ℕ) (q : CFSG.PrimePower) :
    fixedSpace n q →ₗ[fixedField q] q.Extension 2 :=
  (LinearMap.snd (fixedField q) (Fin (n + 1) → fixedField q) (q.Extension 2)).comp
    ((LinearMap.snd (fixedField q) (Fin (n + 1) → fixedField q)
      ((Fin (n + 1) → fixedField q) × q.Extension 2)).comp (linearParameters n q).toLinearMap)

theorem quadratic_parts (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q) :
    fixedQuadraticForm n q v =
      dotProduct (positivePart n q v) (negativePart n q v) + normForm q (anisotropicPart n q v) := by
  have he := quadratic_parameters n q (linearParameters n q v)
  rw [LinearEquiv.symm_apply_apply] at he
  rw [normForm_apply]
  exact he

theorem polar_parts (n : ℕ) (q : CFSG.PrimePower) (v w : fixedSpace n q) :
    (fixedQuadraticForm n q).polarBilin v w =
      dotProduct (positivePart n q v) (negativePart n q w) +
      dotProduct (positivePart n q w) (negativePart n q v) +
        (normForm q).polarBilin (anisotropicPart n q v) (anisotropicPart n q w) := by
  change fixedQuadraticForm n q (v + w) - fixedQuadraticForm n q v - fixedQuadraticForm n q w = _
  rw [quadratic_parts, quadratic_parts, quadratic_parts]
  simp only [map_add, add_dotProduct, dotProduct_add]
  change _ = _ + _ + (normForm q (anisotropicPart n q v + anisotropicPart n q w) -
    normForm q (anisotropicPart n q v) - normForm q (anisotropicPart n q w))
  ring

theorem parameters_positive (n : ℕ) (q : CFSG.PrimePower)
    (x : Fin (n + 1) → fixedField q) :
    linearParameters n q (positiveEmbedding n q x) = (x, (0, 0)) := by
  change linearParameters n q ((linearParameters n q).symm (x, (0, 0))) = _
  exact (linearParameters n q).apply_symm_apply _

theorem parameters_negative (n : ℕ) (q : CFSG.PrimePower)
    (y : Fin (n + 1) → fixedField q) :
    linearParameters n q (negativeEmbedding n q y) = (0, (y, 0)) := by
  change linearParameters n q ((linearParameters n q).symm (0, (y, 0))) = _
  exact (linearParameters n q).apply_symm_apply _

theorem positivePart_positive (n : ℕ) (q : CFSG.PrimePower)
    (x : Fin (n + 1) → fixedField q) : positivePart n q (positiveEmbedding n q x) = x :=
  congrArg Prod.fst (parameters_positive n q x)

theorem negativePart_positive (n : ℕ) (q : CFSG.PrimePower)
    (x : Fin (n + 1) → fixedField q) : negativePart n q (positiveEmbedding n q x) = 0 :=
  congrArg (fun z => z.2.1) (parameters_positive n q x)

theorem anisotropicPart_positive (n : ℕ) (q : CFSG.PrimePower)
    (x : Fin (n + 1) → fixedField q) : anisotropicPart n q (positiveEmbedding n q x) = 0 :=
  congrArg (fun z => z.2.2) (parameters_positive n q x)

theorem positivePart_negative (n : ℕ) (q : CFSG.PrimePower)
    (y : Fin (n + 1) → fixedField q) : positivePart n q (negativeEmbedding n q y) = 0 :=
  congrArg Prod.fst (parameters_negative n q y)

theorem negativePart_negative (n : ℕ) (q : CFSG.PrimePower)
    (y : Fin (n + 1) → fixedField q) : negativePart n q (negativeEmbedding n q y) = y :=
  congrArg (fun z => z.2.1) (parameters_negative n q y)

theorem anisotropicPart_negative (n : ℕ) (q : CFSG.PrimePower)
    (y : Fin (n + 1) → fixedField q) : anisotropicPart n q (negativeEmbedding n q y) = 0 :=
  congrArg (fun z => z.2.2) (parameters_negative n q y)

theorem polar_positive (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q)
    (x : Fin (n + 1) → fixedField q) :
    (fixedQuadraticForm n q).polarBilin v (positiveEmbedding n q x) =
      dotProduct x (negativePart n q v) := by
  rw [polar_parts, positivePart_positive, negativePart_positive, anisotropicPart_positive]
  simp only [dotProduct_zero, map_zero, add_zero, zero_add]

theorem polar_negative (n : ℕ) (q : CFSG.PrimePower) (v : fixedSpace n q)
    (y : Fin (n + 1) → fixedField q) :
    (fixedQuadraticForm n q).polarBilin v (negativeEmbedding n q y) =
      dotProduct (positivePart n q v) y := by
  rw [polar_parts, positivePart_negative, negativePart_negative, anisotropicPart_negative]
  simp only [zero_dotProduct, map_zero, add_zero]

theorem anisotropicPart_zero_positiveSpace (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : v ∈ positiveSpace n q) : anisotropicPart n q v = 0 := by
  obtain ⟨x, rfl⟩ := hv
  exact anisotropicPart_positive n q x

theorem anisotropicPart_zero_negativeSpace (n : ℕ) (q : CFSG.PrimePower)
    (v : fixedSpace n q) (hv : v ∈ negativeSpace n q) : anisotropicPart n q v = 0 := by
  obtain ⟨y, rfl⟩ := hv
  exact anisotropicPart_negative n q y

end SymmetricSubgroupAsymptotics.CFSGTwistedDHyperbolicCoordinates
