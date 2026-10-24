import SymmetricSubgroupAsymptotics.CFSGSymplecticGeneralLinearDouble
import SymmetricSubgroupAsymptotics.CFSGSymplecticSymmetricShearMembership
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryProjectiveEquiv
import SymmetricSubgroupAsymptotics.SymmetricMatrixQuadraticFunctional
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Literal higher-rank symmetric upper shears and their actual GL
congruence normalizer inside the SAME elementary symplectic group.
The full additive group injects into the original projective group in
characteristic two. No parabolic recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelEmbedding

open SymmetricMatrixCongruenceAction SymmetricMatrixQuadraticFunctional
open CFSGSymplecticSerreMatrices
variable (K : Type) [Field K] (m : ℕ) (hm : 0 < m)

def upperHom : Multiplicative (Space (K := K) (m + 1)) →*
    elementaryRootGroup K (m + 1) where
  toFun s := ⟨CFSGMatrixShearUnits.upper s.toAdd.val,
    symmetric_upper_mem K m hm s.toAdd.val s.toAdd.property⟩
  map_one' := by
    apply Subtype.ext
    exact CFSGMatrixShearUnits.upper_zero
  map_mul' s t := by
    apply Subtype.ext
    exact CFSGMatrixShearUnits.upper_add s.toAdd.val t.toAdd.val

theorem upperHom_injective : Function.Injective (upperHom K m hm) := by
  intro s t he
  have hv := congrArg (fun u : elementaryRootGroup K (m + 1) =>
    Matrix.toBlocks₁₂ (u.val : Mat K (m + 1))) he
  change s.toAdd.val = t.toAdd.val at hv
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hv

theorem double_upper_conjugation (A : GeneralLinear (K := K) (m + 1))
    (s : Multiplicative (Space (K := K) (m + 1))) :
    CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K (m + 1) A * upperHom K m hm s *
      (CFSGSymplecticGeneralLinearDouble.doubleIntoElementary K (m + 1) A)⁻¹ =
        upperHom K m hm (Multiplicative.ofAdd (congruenceLinearMap (m + 1) A s.toAdd)) := by
  apply Subtype.ext
  exact CFSGSymplecticGeneralLinearDouble.doubleHom_upper_conjugation K (m + 1) A s.toAdd.val

/-- The literal offdiagonal parameter, expressed as an actual polar cross vector. -/
def offDiagonal (i j : Fin (m + 1)) (t : K) : Space (K := K) (m + 1) :=
  t • cross (m + 1) (Pi.single i 1) (Pi.single j 1)

theorem offDiagonal_entry (i j : Fin (m + 1)) (hij : i ≠ j) (t : K) :
    (offDiagonal K m i j t).val i j = t := by
  change t * ((Pi.single i (1 : K) : Fin (m + 1) → K) i * (Pi.single j (1 : K) : Fin (m + 1) → K) j +
    (Pi.single j (1 : K) : Fin (m + 1) → K) i * (Pi.single i (1 : K) : Fin (m + 1) → K) j) = t
  simp [Pi.single_apply, hij, hij.symm]

theorem offDiagonal_ne_zero (i j : Fin (m + 1)) (hij : i ≠ j)
    (t : K) (ht : t ≠ 0) : offDiagonal K m i j t ≠ 0 := by
  intro he
  have hv := congrArg (fun S : Space (K := K) (m + 1) => S.val i j) he
  have hz : (offDiagonal K m i j t).val i j = 0 := hv
  exact ht ((offDiagonal_entry K m i j hij t).symm.trans hz)

def projectiveUpperHom [CharP K 2] :
    Multiplicative (Space (K := K) (m + 1)) →* elementaryProjective K (m + 1) :=
  (binaryProjectiveEquiv K m).toMonoidHom.comp (upperHom K m hm)

theorem projectiveUpperHom_injective [CharP K 2] :
    Function.Injective (projectiveUpperHom K m hm) :=
  (binaryProjectiveEquiv K m).injective.comp (upperHom_injective K m hm)

end SymmetricSubgroupAsymptotics.CFSGSymplecticHigherSiegelEmbedding
