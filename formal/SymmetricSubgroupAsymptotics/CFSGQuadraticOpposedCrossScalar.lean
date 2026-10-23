import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalCrossPairing
import SymmetricSubgroupAsymptotics.CFSGQuadraticPiecePairing
import SymmetricSubgroupAsymptotics.CFSGBilinearZeroLocusScalar

/-! Actual local linear representatives on disjoint maximal singular
spaces have one common cross-pairing multiplier. The ambient quadratic
space need not be split, and no characteristic restriction is imposed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticOpposedCrossScalar
open CFSGQuadraticMaximalSingularGallery CFSGQuadraticMaximalCrossPairing
open CFSGOrthogonalDIndexQuadraticSubspacePoints CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def sourceCross (Q : QuadraticForm K V) (P Z : Submodule K V) :
    P →ₗ[K] Z →ₗ[K] K := Q.polarBilin.compl₁₂ P.subtype Z.subtype

theorem sourceCross_injective (Q : QuadraticForm K V) (P Z : Submodule K V)
    (hP : MaximalSingular Q P) (hZ : MaximalSingular Q Z) (hdis : Disjoint P Z) :
    Function.Injective (sourceCross Q P Z) := by
  intro x y h
  apply sub_eq_zero.mp
  apply Subtype.ext
  by_contra hne
  obtain ⟨w, hw, _, hp⟩ := opposed_pairing_one Q P Z hP hZ hdis
    (x - y).val (x - y).property hne
  have hz : sourceCross Q P Z (x - y) = 0 := by rw [map_sub, h, sub_self]
  have he := LinearMap.congr_fun hz ⟨w, hw⟩
  change Q.polarBilin (x - y).val w = 0 at he
  exact one_ne_zero (hp.symm.trans he)

theorem sourceCross_nonzero (Q : QuadraticForm K V) (P Z : Submodule K V)
    (hP : MaximalSingular Q P) (hZ : MaximalSingular Q Z) (hdis : Disjoint P Z)
    (hPne : P ≠ ⊥) : ∃ x y, sourceCross Q P Z x y ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPne
  obtain ⟨y, hy, _, hxy⟩ := opposed_pairing_one Q P Z hP hZ hdis x hx hx0
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  change Q.polarBilin x y ≠ 0
  rw [hxy]
  exact one_ne_zero

theorem exists_cross_scalar [FiniteDimensional K V]
    (Q : QuadraticForm K V) (P Z : Submodule K V)
    (hP : MaximalSingular Q P) (hZ : MaximalSingular Q Z) (hdis : Disjoint P Z)
    (hPne : P ≠ ⊥) (f : Points Q ≃ Points Q)
    (horth : ∀ R S, ZeroOn Q.polarBilin (f R).val (f S).val ↔
      ZeroOn Q.polarBilin R.val S.val)
    (F : SemilinearPiece Q f ⟨P, hP.1⟩ (RingEquiv.refl K))
    (G : SemilinearPiece Q f ⟨Z, hZ.1⟩ (RingEquiv.refl K)) :
    ∃ c : K, c ≠ 0 ∧ ∀ (x : P) (y : Z),
      Q.polarBilin (F.map x) (G.map y) = c * Q.polarBilin x.val y.val := by
  let C := Q.polarBilin.compl₁₂ F.map G.map
  obtain ⟨c, hc, he⟩ := CFSGBilinearZeroLocusScalar.exists_nonzero_scalar
    (sourceCross Q P Z) C (sourceCross_injective Q P Z hP hZ hdis)
    (sourceCross_nonzero Q P Z hP hZ hdis hPne)
    (fun x y => piece_pairing_zero_iff Q f horth ⟨P, hP.1⟩ ⟨Z, hZ.1⟩
      (RingEquiv.refl K) (RingEquiv.refl K) F G x y)
  refine ⟨c, hc, ?_⟩
  intro x y
  exact congrArg (fun B : P →ₗ[K] Z →ₗ[K] K => B x y) he

end SymmetricSubgroupAsymptotics.CFSGQuadraticOpposedCrossScalar
