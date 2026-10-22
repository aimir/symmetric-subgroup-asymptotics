import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveRootCardinality
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstCoefficient
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootDegreeSeparation

/-! Every actual selected root parameter is injective, of either sign.
The first coefficient is projected in the original integer root lattice,
before any coefficient-field reduction; no torus-weight separation is
assumed in characteristic two or three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootCardinality CFSGNormTwoRootDegreeSeparation
open CFSGGradedMatrixSupport CFSGGradedMatrixSingleDegreeSpan CFSGGradedQuadraticFirstCoefficient
open CFSGGradedQuadraticUnit
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem selected_root_lattice_first (K : Type) [Field K] (k : Roots A) (a : K) :
    degreePart ell k.val (selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)=
      a • selectedFieldCoefficient A hd hs hp ho K k := by
  rw [selectedRootElement_expansion]
  exact degreePart_quadratic ell k.val _ _
    (supported_smul ell _ _ (selectedFieldCoefficient_support A hd hs hp ho K k) a)
    (supported_smul ell _ _ (selectedSecondCoefficient_support A hd hs hp ho K k) (a^2))
    (root_val_ne_zero A k) (root_val_ne_double A k k)

theorem selected_rootHom_injective (K : Type) [Field K] (k : Roots A) :
    Function.Injective (selectedRootHom A hd hs hp ho K k) := by
  intro a b he
  change selectedRootElement A hd hs hp ho K k a.toAdd=
    selectedRootElement A hd hs hp ho K k b.toAdd at he
  have hh := congrArg (fun u : (CoordMat A hd hs hp ho K)ˣ=>degreePart ell k.val
    (u : CoordMat A hd hs hp ho K)) he
  dsimp only at hh
  rw [selected_root_lattice_first,selected_root_lattice_first] at hh
  exact congrArg Multiplicative.ofAdd
    (smul_left_injective K (selectedFieldCoefficient_ne_zero A hd hs hp ho K k) hh)

theorem selected_root_one_ne_one (K : Type) [Field K] (k : Roots A) :
    selectedRootElement A hd hs hp ho K k 1≠1 := by
  intro he
  have hh := congrArg (fun u : (CoordMat A hd hs hp ho K)ˣ=>degreePart ell k.val
    (u : CoordMat A hd hs hp ho K)) he
  dsimp only at hh
  rw [selected_root_lattice_first] at hh
  change (1:K) • selectedFieldCoefficient A hd hs hp ho K k=
    degreePart ell k.val (1 : CoordMat A hd hs hp ho K) at hh
  rw [degreePart_one_zero ell k.val (root_val_ne_zero A k),one_smul] at hh
  exact selectedFieldCoefficient_ne_zero A hd hs hp ho K k hh

theorem rootSubgroup_card (K : Type) [Field K] (k : Roots A) :
    Nat.card (CFSGNormTwoCoordinateRootSubgroup.rootSubgroup A hd hs hp ho K k)=Nat.card K := by
  rw [←selectedRootHom_range]
  calc
    _=Nat.card (Multiplicative K) := (Nat.card_congr
      (MonoidHom.ofInjective (selected_rootHom_injective A hd hs hp ho K k)).toEquiv).symm
    _=Nat.card K := Nat.card_congr (Multiplicative.toAdd : Multiplicative K≃K)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
