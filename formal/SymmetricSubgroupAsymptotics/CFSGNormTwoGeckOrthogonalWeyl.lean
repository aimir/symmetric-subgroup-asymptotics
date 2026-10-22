import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSignedCommutation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalCollecting

/-! Orthogonal actual simple Weyl WORDS commute, over every coefficient
ring. All four signed rational brackets are discharged from the original
Serre data before transporting both parameter groups integrally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckRationalWeylCollecting
open CFSGNormTwoGeckOrthogonalCollecting
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

theorem signed_lie_zero (i j : Fin r) (hij : cartan b s i j=0) (e f : Bool) :
    ⁅fieldRoot D ℚ e i,fieldRoot D ℚ f j⁆=0 := by
  have hne : i≠j := indices_ne_of_cartan_zero A hs hp b s i j hij
  cases e <;> cases f
  · exact lie_of_cartan_zero A hs hp b s i j hij
  · rw [rational_E_eq,rational_F_eq,EF,if_neg hne]
  · exact F_E_ne A hs hp b s i j hne
  · simp only [rational_F_eq]
    have hh := serreF b s i j
    simpa only [hij,neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] using hh

theorem orthogonal_signed_roots (K : Type*) [CommRing K]
    (i j : Fin r) (hij : cartan b s i j=0) (e f : Bool) (t a : K) :
    Commute (canonicalRoot D K e i t) (canonicalRoot D K f j a) :=
  CFSGSerreQuadraticSignedCommutation.roots_commute D K e f i j
    (signed_lie_zero A hs hp b s i j hij e f) t a

theorem orthogonal_weyl_root (K : Type*) [CommRing K]
    (i j : Fin r) (hij : cartan b s i j=0) (f : Bool) (a : K) :
    Commute (canonicalWeyl D K i) (canonicalRoot D K f j a) := by
  exact ((orthogonal_signed_roots A hs hp b s K i j hij false f 1 a).mul_left
    (orthogonal_signed_roots A hs hp b s K i j hij true f (-1) a)).mul_left
    (orthogonal_signed_roots A hs hp b s K i j hij false f 1 a)

theorem orthogonal_weyls (K : Type*) [CommRing K]
    (i j : Fin r) (hij : cartan b s i j=0) :
    Commute (canonicalWeyl D K i) (canonicalWeyl D K j) := by
  exact ((orthogonal_weyl_root A hs hp b s K i j hij false 1).mul_right
    (orthogonal_weyl_root A hs hp b s K i j hij true (-1))).mul_right
    (orthogonal_weyl_root A hs hp b s K i j hij false 1)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
