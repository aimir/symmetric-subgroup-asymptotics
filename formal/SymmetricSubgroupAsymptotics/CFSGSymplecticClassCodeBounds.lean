import SymmetricSubgroupAsymptotics.CFSGSymplecticPrimaryCodeData
import SymmetricSubgroupAsymptotics.GeneralLinearPrimaryFiniteCode

/-! Genuine finite primary codes yield numerical class bounds for the
SAME original elementary symplectic group. The code is defined only on
fixed-free elements, so no fallback or nonemptiness premise is needed.
The actual polynomial range, exponent mass and fusion are all proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticClassCodeBounds
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticPrimaryCodeData CFSGSymplecticFixedFreeClassCodes
variable (K : Type) [Field K]

abbrev ClassCode (r N : ℕ) := GeneralLinearPrimaryFiniteCode.Code
  (fun p : PolynomialIndex K r => p.val) N

instance finiteClassCode [Finite K] (r N : ℕ) : Finite (ClassCode K r N) := by
  letI := Fintype.ofFinite (PolynomialIndex K r)
  infer_instance

theorem classCode_card_le [Finite K] [CharP K 2] (r N : ℕ) :
    Nat.card (ClassCode K r N) ≤ Nat.card K ^ r * 2^(N-1) := by
  letI := Fintype.ofFinite (PolynomialIndex K r)
  exact (GeneralLinearPrimaryFiniteCode.card_le
    (fun p : PolynomialIndex K r => p.val) N).trans
      (Nat.mul_le_mul_right _ (polynomialIndex_card_le K r))

def binaryCode [Finite K] [CharP K 2] (hK : Nat.card K = 2) (r : ℕ)
    (g : FixedFreeElement K r) : ClassCode K r r :=
  GeneralLinearPrimaryFiniteCode.code (fun p : PolynomialIndex K r => p.val) r
    (linearUnit K r g.val) (polynomialIndex K r g.val)
    (linearUnit_charpoly_eq_index K r g.val) (normalizedFactor_mass_le_binary K hK r g)

def generalCode (r : ℕ) (g : FixedFreeElement K r) : ClassCode K r (2*r) :=
  GeneralLinearPrimaryFiniteCode.code (fun p : PolynomialIndex K r => p.val) (2*r)
    (linearUnit K r g.val) (polynomialIndex K r g.val)
    (linearUnit_charpoly_eq_index K r g.val) (normalizedFactor_mass_le K r g.val)

private theorem natural_isConj_of_unit_isConj (r : ℕ)
    (g h : elementaryRootGroup K r) (hc : IsConj (linearUnit K r g) (linearUnit K r h)) :
    IsConj (naturalLinearHom K r g) (naturalLinearHom K r h) := by
  have hh := (LinearMap.GeneralLinearGroup.generalLinearEquiv K
    (Index r → K)).toMonoidHom.map_isConj hc
  exact hh

theorem binaryCode_isConj [Finite K] [CharP K 2] (hK : Nat.card K = 2) (r : ℕ)
    (g h : FixedFreeElement K r) (he : binaryCode K hK r g = binaryCode K hK r h) :
    IsConj (naturalLinearHom K r g.val) (naturalLinearHom K r h.val) := by
  apply natural_isConj_of_unit_isConj K r g.val h.val
  exact GeneralLinearPrimaryFiniteCode.isConj_of_code_eq
    (fun p : PolynomialIndex K r => p.val) r
    (linearUnit K r g.val) (linearUnit K r h.val)
    (polynomialIndex K r g.val) (polynomialIndex K r h.val)
    (linearUnit_charpoly_eq_index K r g.val) (linearUnit_charpoly_eq_index K r h.val)
    (normalizedFactor_mass_le_binary K hK r g) (normalizedFactor_mass_le_binary K hK r h) he

theorem generalCode_isConj (r : ℕ) (g h : FixedFreeElement K r)
    (he : generalCode K r g = generalCode K r h) :
    IsConj (naturalLinearHom K r g.val) (naturalLinearHom K r h.val) := by
  apply natural_isConj_of_unit_isConj K r g.val h.val
  exact GeneralLinearPrimaryFiniteCode.isConj_of_code_eq
    (fun p : PolynomialIndex K r => p.val) (2*r)
    (linearUnit K r g.val) (linearUnit K r h.val)
    (polynomialIndex K r g.val) (polynomialIndex K r h.val)
    (linearUnit_charpoly_eq_index K r g.val) (linearUnit_charpoly_eq_index K r h.val)
    (normalizedFactor_mass_le K r g.val) (normalizedFactor_mass_le K r h.val) he

theorem class_card_le_binary [Finite K] [CharP K 2] (hK : Nat.card K = 2) (r : ℕ) :
    Nat.card (ConjClasses (elementaryRootGroup K (r+1))) ≤
      Nat.card (ConjClasses (pointStabilizer K r)) + 2^(2*r+1) := by
  have h := class_card_le_point_add_code K r (binaryCode K hK (r+1))
    (binaryCode_isConj K hK (r+1))
  have hc := classCode_card_le K (r+1) (r+1)
  rw [hK] at hc
  have hp : (2 : ℕ)^(r+1)*2^(r+1-1) = 2^(2*r+1) := by
    rw [←pow_add]
    congr 1
    omega
  rw [hp] at hc
  exact h.trans (Nat.add_le_add_left hc _)

theorem class_card_le_general [Finite K] [CharP K 2] (r : ℕ) :
    Nat.card (ConjClasses (elementaryRootGroup K (r+1))) ≤
      Nat.card (ConjClasses (pointStabilizer K r)) +
        Nat.card K ^ (r+1) * 2^(2*(r+1)-1) := by
  exact (class_card_le_point_add_code K r (generalCode K (r+1))
    (generalCode_isConj K (r+1))).trans
      (Nat.add_le_add_left (classCode_card_le K (r+1) (2*(r+1))) _)

end SymmetricSubgroupAsymptotics.CFSGSymplecticClassCodeBounds
