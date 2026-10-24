import SymmetricSubgroupAsymptotics.CFSGFFourOriginalRootCoordinateOrthogonality

/-! Weight-zero Cartan coefficient functionals. Composing a positive
simple unit coordinate with ad(E_i) gives -A[j,i] on H_j and vanishes on
every signed root image. This uses actual source weights and avoids a
new matrix diagonal-entry certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalCartanCoordinateOrthogonality
open CFSG.Models.Chevalley CFSGFFourSerreMatrices
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalRootFamilyProfile
open CFSGFFourOriginalSimpleCoordinateWeights CFSGFFourOriginalSimpleImageCoordinates
open CFSGFFourOriginalSourceWordWeights CFSGFFourOriginalSeparatingCartan
open CFSGRationalLieWeightCoordinates CFSGNormTwoRootPairing
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local notation "A" => CartanMatrix.F₄

def cartanRawCoordinate (i:Fin 4) : Mat→ₗ[ℚ]ℚ :=
  (simpleCoordinate i).comp (LieAlgebra.ad ℚ Mat (positive i))

theorem cartan_coordinate_H (i b:Fin 4) :
    cartanRawCoordinate i (rationalRepresentation (generator A (.H b)))=(-A b i:ℤ) := by
  change simpleCoordinate i ⁅positive i,rationalRepresentation (generator A (.H b))⁆=
    ((-A b i:ℤ):ℚ)
  rw [rationalRepresentation_H]
  have he:⁅cartan b,positive i⁆=(A b i:ℚ) • positive i := by
    simpa only [Int.cast_smul_eq_zsmul] using HE b i
  have hu:simpleCoordinate i (positive i)=1:=by
    simpa only [if_pos rfl] using positive_coordinate i i
  rw [←lie_skew (positive i) (cartan b),he,map_neg,map_smul,hu]
  simp only [smul_eq_mul,mul_one,Int.cast_neg]

theorem cartan_coordinate_root (i:Fin 4) (neg:Bool) (j:Fin 24) :
    cartanRawCoordinate i (rationalRepresentation (rootVectors neg j).val)=0 := by
  have he:⁅rationalRepresentation testCartan,positive i⁆=
      (testWeight (simpleIndex i):ℚ) • positive i := by
    have h:=congrArg rationalRepresentation (CFSGFFourOriginalSourceWordWeights.simple_weight false i)
    change rationalRepresentation ⁅testCartan,generator A (.E i)⁆=
      rationalRepresentation ((testWeight (simpleIndex i):ℚ) • generator A (.E i)) at h
    simpa only [LieHom.map_lie,map_smul,rationalRepresentation_E] using h
  have hx:⁅rationalRepresentation testCartan,rationalRepresentation (rootVectors neg j).val⁆=
      (signedTestWeight neg j:ℚ) • rationalRepresentation (rootVectors neg j).val := by
    simpa only [LieHom.map_lie,map_smul] using
      congrArg rationalRepresentation (CFSGFFourOriginalSourceWordWeights.root_weight neg j)
  have hmu:(signedTestWeight neg j:ℚ)≠0:=by exact_mod_cast signedTestWeight_ne_zero neg j
  have hne:(testWeight (simpleIndex i):ℚ)+(signedTestWeight neg j:ℚ)≠
      (testWeight (simpleIndex i):ℚ) := by
    intro h
    exact hmu (add_left_cancel (h.trans (add_zero _).symm))
  exact coordinate_zero_of_weights_ne (rationalRepresentation testCartan) (simpleCoordinate i)
    ((testWeight (simpleIndex i):ℚ)+(signedTestWeight neg j:ℚ))
    (testWeight (simpleIndex i):ℚ) (simple_testCartan_coordinate i)
    ⁅positive i,rationalRepresentation (rootVectors neg j).val⁆
    (bracket_weight _ _ _ _ _ he hx) hne

def cartanEntry (i:Fin 4) : BasisIndex→ℤ
  | .inl _=>0
  | .inr b=> -A b i

theorem cartan_coordinate_vector (i:Fin 4) (k:BasisIndex) :
    cartanRawCoordinate i (rationalRepresentation (vectors k))=(cartanEntry i k:ℚ) := by
  cases k with
  | inl z=>exact cartan_coordinate_root i z.1 z.2
  | inr b=>exact cartan_coordinate_H i b

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalCartanCoordinateOrthogonality
