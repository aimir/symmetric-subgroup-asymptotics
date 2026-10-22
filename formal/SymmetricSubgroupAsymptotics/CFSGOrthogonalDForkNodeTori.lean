import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus

/-! Literal four-root torus words at the two orthogonal terminal nodes.
These identities concern the natural elementary group, and do not assert
rank-one relations on the original Serre source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkNodeTori
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDGenerationForkTorus CFSGOrthogonalDGenerationSLDouble
open CFSGTypeAElementaryMatrices
variable (K : Type) [Field K]

def nodeTorus (s : ℕ) (i : Fin (s + 2)) (c : Kˣ) : elementaryRootGroup K (s + 2) :=
  rootElement K (s + 2) false i ((c : K) - 1) *
    rootElement K (s + 2) true i 1 *
    rootElement K (s + 2) false i ((c : K)⁻¹ - 1) *
    rootElement K (s + 2) true i (-(c : K))

theorem double_elementary_pen (s : ℕ) (a : K) :
    doubleIntoElementary K (s + 2) (elementary (pen_ne_last s) a) =
      rootElement K (s + 2) false (pen s) a := by
  apply Subtype.ext
  apply Units.ext
  rw [show ((doubleIntoElementary K (s + 2) (elementary (pen_ne_last s) a)).val :
      Mat K (s + 2)) = (doubleHom K (s + 2) (elementary (pen_ne_last s) a) :
        Mat K (s + 2)) from rfl, doubleHom_elementary_val]
  change 1 + a • chainMatrix K (s + 2) (pen s) (last s) =
    1 + a • positive K (s + 2) (pen s)
  have hi : (pen s).val + 1 < s + 2 := by dsimp [pen]; omega
  have hn : (⟨(pen s).val + 1, hi⟩ : Fin (s + 2)) = last s := by
    apply Fin.ext
    rfl
  rw [positive, dif_pos hi, hn]
  rfl

theorem double_elementary_pen_reverse (s : ℕ) (a : K) :
    doubleIntoElementary K (s + 2) (elementary (Ne.symm (pen_ne_last s)) a) =
      rootElement K (s + 2) true (pen s) a := by
  apply Subtype.ext
  apply Units.ext
  rw [show ((doubleIntoElementary K (s + 2)
      (elementary (Ne.symm (pen_ne_last s)) a)).val : Mat K (s + 2)) =
      (doubleHom K (s + 2) (elementary (Ne.symm (pen_ne_last s)) a) :
        Mat K (s + 2)) from rfl, doubleHom_elementary_val]
  change 1 + a • chainMatrix K (s + 2) (last s) (pen s) =
    1 + a • negative K (s + 2) (pen s)
  have hi : (pen s).val + 1 < s + 2 := by dsimp [pen]; omega
  have hn : (⟨(pen s).val + 1, hi⟩ : Fin (s + 2)) = last s := by
    apply Fin.ext
    rfl
  simp only [negative, positive, dif_pos hi, hn, Matrix.transpose_sub,
    Matrix.transpose_single, chainMatrix]

theorem nodeTorus_pen (s : ℕ) (c : Kˣ) :
    nodeTorus K s (pen s) c =
      doubleIntoElementary K (s + 2) (CFSGTypeARootTorus.torus (pen_ne_last s) c) := by
  simp only [CFSGTypeARootTorus.torus, map_mul, double_elementary_pen,
    double_elementary_pen_reverse, nodeTorus]

theorem nodeTorus_last (s : ℕ) (c : Kˣ) :
    nodeTorus K s (last s) c = forkTorus K s c := rfl

theorem nodeTorus_pen_val (s : ℕ) (c : Kˣ) :
    ((nodeTorus K s (pen s) c).val : Mat K (s + 2)) =
      Matrix.diagonal (chainDiagonal K s c) := by
  rw [nodeTorus_pen]
  exact doubleMatrix_torus K s c

theorem nodeTorus_last_val (s : ℕ) (c : Kˣ) :
    ((nodeTorus K s (last s) c).val : Mat K (s + 2)) =
      Matrix.diagonal (forkDiagonal K s c) := forkTorus_coe K s c

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkNodeTori
