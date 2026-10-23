import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairingReduced

/-! A genuine finite based norm-two realization for the literal D4
Cartan table. Positive definiteness and an integral Gram factor are
inherited from the explicit principal E6 subdiagram [2,3,4,1]. No root
enumeration or named-group comparison is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityD4NormTwo
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoFinite

def d4Index : Fin 4→Fin 6:=![2,3,4,1]

theorem d4Index_injective : Function.Injective d4Index := by decide

theorem D4_principal : CartanMatrix.D 4=CartanMatrix.E₆.submatrix d4Index d4Index := by
  decide

theorem D4_positive_definite : (rationalMatrix (CartanMatrix.D 4)).PosDef := by
  have he : rationalMatrix (CartanMatrix.D 4)=
      ((Int.castRingHom ℚ).mapMatrix CartanMatrix.E₆).submatrix d4Index d4Index := by
    ext i j
    exact congrArg (fun z : ℤ=>(z:ℚ)) (congrFun (congrFun D4_principal i) j)
  rw [he]
  exact E6_positive_definite.submatrix d4Index_injective

def gramFour : Matrix (Fin 8) (Fin 4) ℤ:=gramSix.submatrix id d4Index

theorem gramFour_identity : gramFour.transpose*gramFour=(4:ℤ) • CartanMatrix.D 4 := by
  calc
    gramFour.transpose*gramFour=(gramSix.transpose*gramSix).submatrix d4Index d4Index := by
      ext i j
      rfl
    _=(4:ℤ) • CartanMatrix.D 4 := by
      rw [gramSix_identity,D4_principal]
      rfl

instance D4_roots_finite : Finite (Roots (CartanMatrix.D 4)) :=
  (CFSGIntegralGramRootFiniteness.finite_norm_two (CartanMatrix.D 4) gramFour 4
    (by decide) gramFour_identity D4_positive_definite).to_subtype

instance D4_roots_fintype : Fintype (Roots (CartanMatrix.D 4)):=Fintype.ofFinite _
local instance D4_roots_decidableEq : DecidableEq (Roots (CartanMatrix.D 4)):=Classical.decEq _

theorem D4_connected : ∀ i j,
    Relation.ReflTransGen (fun a b=>CartanMatrix.D 4 a b≠0) i j := by
  have hc : ∀ i : Fin 4, Relation.ReflTransGen (fun a b=>CartanMatrix.D 4 a b≠0) i 1 := by
    intro i
    fin_cases i
    · exact .single (by decide)
    · exact .refl
    · exact .single (by decide)
    · exact .single (by decide)
  have hr : Symmetric (fun a b : Fin 4=>CartanMatrix.D 4 a b≠0) := by
    intro a b hab
    have he:=congrFun (congrFun (CartanMatrix.D_transpose 4) a) b
    change CartanMatrix.D 4 b a=CartanMatrix.D 4 a b at he
    rwa [he]
  intro i j
  exact (hc i).trans ((Relation.ReflTransGen.symmetric hr) (hc j))

abbrev Pairing:=rootPairing (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite

instance D4_irreducible : Pairing.IsIrreducible :=
  rootPairing_isIrreducible_of_connected (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite D4_connected

def Base : Pairing.Base:=coordinateBase (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
  (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)

def Index : Fin 4≃Base.support:=coordinateIndexEquiv _ _ _ _ _

theorem cartan_eq : CFSGGeckSerreRepresentation.cartan Base Index=CartanMatrix.D 4 := by
  ext i j
  exact coordinate_cartan_transpose _ _ _ _ _ i j

end SymmetricSubgroupAsymptotics.CFSGTrialityD4NormTwo
