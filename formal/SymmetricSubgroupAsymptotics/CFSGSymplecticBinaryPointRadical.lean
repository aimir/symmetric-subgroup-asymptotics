import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergWords
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergCoordinates
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryProjectiveEquiv
import Mathlib.Algebra.CharP.Two

/-! In characteristic two the point radical has an additive chart
(v,c) -> shear(v,c+Q0(v)). Its ACTUAL central coordinate is c, not the
-2c which vanishes in the odd Heisenberg chart. All elements are literal
transvection words in the same elementary symplectic group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointRadical

open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticHeisenbergWords CFSGSymplecticHeisenbergOperators
open CFSGSymplecticHeisenbergCoordinates CFSGHeisenbergCoordinateGroup
variable (K : Type) [Field K] [CharP K 2]

abbrev Coordinates (m : ℕ) := ((Fin m → K) × (Fin m → K)) × K

def firstVector (m : ℕ) : Index (m+1) → K := Pi.single (Sum.inl 0) 1

def tail (m : ℕ) (v : (Fin m → K) × (Fin m → K)) : Index (m+1) → K :=
  tailVector (⟨v.1,v.2,0⟩ : Element K m)

def parameter (m : ℕ) (a : Coordinates K m) : K :=
  a.2+dotProduct a.1.1 a.1.2

omit [CharP K 2] in
private theorem tail_zero (m : ℕ) : tail K m 0 = 0 := tailVector_one

omit [CharP K 2] in
private theorem tail_add (m : ℕ) (v w : (Fin m → K) × (Fin m → K)) :
    tail K m (v+w) = tail K m v+tail K m w := by
  change tailVector ((⟨v.1,v.2,0⟩ : Element K m) * ⟨w.1,w.2,0⟩) =
    tailVector (⟨v.1,v.2,0⟩ : Element K m)+tailVector (⟨w.1,w.2,0⟩ : Element K m)
  exact tailVector_mul _ _

omit [CharP K 2] in
private theorem tail_orthogonal (m : ℕ) (v : (Fin m → K) × (Fin m → K)) :
    pairing (m+1) (firstVector K m) (tail K m v) = 0 :=
  tailVector_orthogonal_first (⟨v.1,v.2,0⟩ : Element K m)

omit [CharP K 2] in
private theorem tail_pairing (m : ℕ) (v w : (Fin m → K) × (Fin m → K)) :
    pairing (m+1) (tail K m v) (tail K m w) =
      dotProduct v.1 w.2-dotProduct v.2 w.1 :=
  pairing_tailVectors (⟨v.1,v.2,0⟩ : Element K m) (⟨w.1,w.2,0⟩ : Element K m)

private theorem parameter_add (m : ℕ) (a b : Coordinates K m) :
    parameter K m (a+b) = parameter K m a+parameter K m b+
      pairing (m+1) (tail K m a.1) (tail K m b.1) := by
  rw [tail_pairing]
  simp only [parameter, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add,
    CharTwo.sub_eq_add]
  rw [dotProduct_comm b.1.1 a.1.2]
  ring

def elementaryHom (m : ℕ) (hm : 0 < m) :
    Multiplicative (Coordinates K m) →* elementaryRootGroup K (m+1) where
  toFun a := shearElement K m hm (firstVector K m) (tail K m a.toAdd.1)
    (parameter K m a.toAdd)
  map_one' := by
    apply elementary_ext_of_mulVec K
    intro x
    change ((shearElement K m hm (firstVector K m) (tail K m 0)
      (parameter K m 0)).val : Mat K (m+1)) *ᵥ x = (1 : Mat K (m+1)) *ᵥ x
    rw [shearElement_apply, tail_zero]
    have hp : parameter K m 0 = 0 := by simp [parameter]
    rw [hp, shear_zero_vector, transvection_zero, Matrix.one_mulVec]
    rfl
  map_mul' a b := by
    change shearElement K m hm (firstVector K m) (tail K m (a.toAdd.1+b.toAdd.1))
      (parameter K m (a.toAdd+b.toAdd)) =
      shearElement K m hm (firstVector K m) (tail K m a.toAdd.1) (parameter K m a.toAdd) *
        shearElement K m hm (firstVector K m) (tail K m b.toAdd.1) (parameter K m b.toAdd)
    rw [tail_add, parameter_add]
    exact (shearElement_mul K m hm (firstVector K m) (tail K m a.toAdd.1)
      (tail K m b.toAdd.1) (parameter K m a.toAdd) (parameter K m b.toAdd)
      (tail_orthogonal K m a.toAdd.1) (tail_orthogonal K m b.toAdd.1)).symm

theorem elementaryHom_apply (m : ℕ) (hm : 0 < m)
    (a : Multiplicative (Coordinates K m)) (x : Index (m+1) → K) :
    ((elementaryHom K m hm a).val : Mat K (m+1)) *ᵥ x =
      shear (m+1) (firstVector K m) (tail K m a.toAdd.1) (parameter K m a.toAdd) x :=
  shearElement_apply K m hm (firstVector K m) (tail K m a.toAdd.1) x (parameter K m a.toAdd)

theorem elementaryHom_central (m : ℕ) (hm : 0 < m) (c : K) :
    elementaryHom K m hm (Multiplicative.ofAdd (0,c)) = firstLongRoot K m c := by
  apply elementary_ext_of_mulVec K
  intro x
  rw [elementaryHom_apply]
  change shear (m+1) (firstVector K m) (tail K m 0) (c+dotProduct 0 0) x = _
  rw [tail_zero, zero_dotProduct, add_zero, shear_zero_vector]
  exact (firstLongRoot_mulVec_eq_transvection m c x).symm

def projectiveHom (m : ℕ) (hm : 0 < m) :
    Multiplicative (Coordinates K m) →* elementaryProjective K (m+1) :=
  (binaryProjectiveEquiv K m).toMonoidHom.comp (elementaryHom K m hm)

theorem projective_central_ne_one (m : ℕ) (hm : 0 < m) (c : K) (hc : c ≠ 0) :
    projectiveHom K m hm (Multiplicative.ofAdd (0,c)) ≠ 1 := by
  intro he
  have he' : elementaryHom K m hm (Multiplicative.ofAdd (0,c)) = 1 :=
    (binaryProjectiveEquiv K m).injective (he.trans (binaryProjectiveEquiv K m).map_one.symm)
  rw [elementaryHom_central] at he'
  have hentry := congrArg (fun g : elementaryRootGroup K (m+1) =>
    (g.val : Mat K (m+1)) (Sum.inl 0) (Sum.inr 0)) he'
  change ((firstLongRoot K m c).val : Mat K (m+1)) (Sum.inl 0) (Sum.inr 0) =
    (1 : Mat K (m+1)) (Sum.inl 0) (Sum.inr 0) at hentry
  rw [firstLongRoot_coe] at hentry
  apply hc
  simpa [Matrix.transvection, Matrix.smul_single, Matrix.one_apply] using hentry

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointRadical
