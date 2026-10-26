import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords

/-! Literal recovery of the three original generators from the SAME selected
M12 pair. The primary's one-pair Schreier diagnostic supplied words of
length25/31/33 (JSON SHAd9b6097d1d210e04c92a3c5a22fcce4dd60d87c0a8113c532843035c7ed16365).
These whole12-point kernel proofs supply the mathematical obligation.
The already certified short x/y table images avoid re-expanding the long
original y word at every occurrence. No proof resource cap is increased. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveryWords
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords

def recoverAWord {G : Type*} [Group G] (u v : G) : G :=
  v*u*v⁻¹*u * v*u*v⁻¹*u * v⁻¹*u*v⁻¹*u * v*u*v⁻¹*u *
    v⁻¹*u*v⁻¹*u * v*u*v*u * v⁻¹

def recoverBWord {G : Type*} [Group G] (u v : G) : G :=
  v⁻¹*u*v*u * v⁻¹*u*v⁻¹*u * v*u*v*u * v*u*v⁻¹*u *
    v⁻¹*u*v*u * v⁻¹*u*v*u * v*u*v*u * v*u*v⁻¹

def recoverCWord {G : Type*} [Group G] (u v : G) : G :=
  v*u*v*u * v*u*v*u * v⁻¹*u*v*u * v*u*v*u *
    v⁻¹*u*v⁻¹*u * v*u*v*u * v⁻¹*u*v*u * v*u*v⁻¹*u * v

theorem recoverAWord_eq_originalA : recoverAWord x y = originalA := by
  apply Subtype.ext
  change recoverAWord x.val y.val = m12a
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem recoverBWord_eq_originalB : recoverBWord x y = originalB := by
  apply Subtype.ext
  change recoverBWord x.val y.val = m12b
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

theorem recoverCWord_eq_originalC : recoverCWord x y = originalC := by
  apply Subtype.ext
  change recoverCWord x.val y.val = m12c
  rw [x_coe_eq, y_coe_eq]
  ext i
  fin_cases i <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveryWords
