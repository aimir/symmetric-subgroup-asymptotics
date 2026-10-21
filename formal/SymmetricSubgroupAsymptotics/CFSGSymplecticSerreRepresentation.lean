import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreCartanAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticSerrePowers
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation

/-! A genuine representation of the pinned rational type-C Serre quotient
by the literal standard symplectic simple-root matrices. Injectivity of the
Serre quotient is neither assumed nor asserted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : ℕ)

theorem map_positive (i : Fin r) :
    f.mapMatrix (positive R r i) = positive S r i := by
  by_cases hi : i.val + 1 < r
  · simp only [positive, dif_pos hi]
    rw [map_sub]
    change (Matrix.single _ _ (1 : R)).map f - (Matrix.single _ _ (1 : R)).map f = _
    simp only [Matrix.map_single, map_one]
  · simp only [positive, dif_neg hi]
    change (Matrix.single _ _ (1 : R)).map f = _
    simp only [Matrix.map_single, map_one]

theorem map_negative (i : Fin r) :
    f.mapMatrix (negative R r i) = negative S r i := by
  change (positive R r i).transpose.map f = (positive S r i).transpose
  rw [Matrix.transpose_map]
  exact congrArg Matrix.transpose (map_positive f r i)

theorem map_cartan (i : Fin r) : f.mapMatrix (cartan R r i) = cartan S r i := by
  simp only [cartan, Ring.lie_def, map_sub, map_mul, map_positive, map_negative]

theorem HE (i j : Fin r) :
    ⁅cartan R r i, positive R r j⁆ = CartanMatrix.B r i j • positive R r j := by
  have h := congrArg (Int.castRingHom R).mapMatrix (HE_integer r i j)
  simpa only [Ring.lie_def, map_sub, map_mul, map_zsmul, map_cartan, map_positive] using h

theorem HF (i j : Fin r) :
    ⁅cartan R r i, negative R r j⁆ = -(CartanMatrix.B r i j • negative R r j) := by
  have h := congrArg (Int.castRingHom R).mapMatrix (HF_integer r i j)
  simpa only [Ring.lie_def, map_sub, map_mul, map_neg, map_zsmul, map_cartan, map_negative] using h

def rationalSymplecticRepresentation (r : ℕ) :
    CFSG.Models.Chevalley.RationalLie (CartanMatrix.C r).transpose →ₗ⁅ℚ⁆ Mat ℚ r :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ r) (positive ℚ r) (negative ℚ r) (CartanMatrix.C r).transpose
    (cartan_cartan ℚ r) (EF ℚ r)
    (fun i j => by simpa only [typeC_transpose] using HE (R := ℚ) r i j)
    (fun i j => by simpa only [typeC_transpose] using HF (R := ℚ) r i j)
    (fun i j => by simpa only [typeC_transpose] using positive_serre ℚ r i j)
    (fun i j => by simpa only [typeC_transpose] using negative_serre ℚ r i j)

@[simp] theorem rationalSymplecticRepresentation_H (r : ℕ) (i : Fin r) :
    rationalSymplecticRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.H i)) = cartan ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalSymplecticRepresentation_E (r : ℕ) (i : Fin r) :
    rationalSymplecticRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.E i)) = positive ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalSymplecticRepresentation_F (r : ℕ) (i : Fin r) :
    rationalSymplecticRepresentation r
      (CFSG.Models.Chevalley.generator (CartanMatrix.C r).transpose
        (CartanMatrix.Generators.F i)) = negative ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
