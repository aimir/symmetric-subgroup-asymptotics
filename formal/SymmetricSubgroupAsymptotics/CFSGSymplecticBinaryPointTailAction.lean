import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointRadical
import SymmetricSubgroupAsymptotics.BinaryQuadraticLiftAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformTail
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergVectorAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergShearEquivariance
import SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound

/-! The actual smaller elementary symplectic matrices act on the binary
point chart by its genuine quadratic correction. Natural form
preservation discharges the lift's hypothesis; actual shear conjugation
discharges covariance. No Levi recognition or assumed action occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticStabilizerCoordinates CFSGSymplecticHeisenbergWords
open CFSGSymplecticHeisenbergCoordinates CFSGHeisenbergCoordinateGroup
open CFSGSymplecticUniformTail CFSGSymplecticHeisenbergVectorAction
open CFSGSymplecticHeisenbergShearEquivariance BinaryQuadraticRefinementTransvections
variable (K : Type) [Field K] [CharP K 2]

private def naturalLinearHom (m : ℕ) : elementaryRootGroup K m →*
    ((Index m → K) ≃ₗ[K] (Index m → K)) :=
  MatrixUnitBilinearIsometryOrderBound.naturalLinearHom K (Index m) (elementaryRootGroup K m)

def vectorLinearHom (m : ℕ) : elementaryRootGroup K m →*
    (((Fin m → K) × (Fin m → K)) ≃ₗ[K] ((Fin m → K) × (Fin m → K))) where
  toFun A := ((vectorEquiv K m).trans (naturalLinearHom K m A)).trans (vectorEquiv K m).symm
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (vectorEquiv K m).symm (naturalLinearHom K m 1 (vectorEquiv K m v)) = v
    rw [map_one]
    exact (vectorEquiv K m).symm_apply_apply v
  map_mul' A B := by
    apply LinearEquiv.ext
    intro v
    change (vectorEquiv K m).symm (naturalLinearHom K m (A*B) (vectorEquiv K m v)) =
      (vectorEquiv K m).symm (naturalLinearHom K m A (vectorEquiv K m
        ((vectorEquiv K m).symm (naturalLinearHom K m B (vectorEquiv K m v)))))
    rw [(vectorEquiv K m).apply_symm_apply, map_mul]
    rfl

omit [CharP K 2] in
theorem vectorLinearHom_apply (m : ℕ) (A : elementaryRootGroup K m)
    (v : (Fin m → K) × (Fin m → K)) :
    vectorLinearHom K m A v =
      (vectorEquiv K m).symm ((A.val : Mat K m) *ᵥ vectorEquiv K m v) := rfl

private theorem vectorEquiv_pairing (m : ℕ)
    (v w : (Fin m → K) × (Fin m → K)) :
    pairing m (vectorEquiv K m v) (vectorEquiv K m w) = polar v w := by
  have hh := pairing_tailVectors (⟨v.1,v.2,0⟩ : Element K m)
    (⟨w.1,w.2,0⟩ : Element K m)
  change pairing (m+1) (tailExtend m (vectorEquiv K m v))
    (tailExtend m (vectorEquiv K m w)) = dotProduct v.1 w.2-dotProduct v.2 w.1 at hh
  rw [pairing_tailExtend, CharTwo.sub_eq_add] at hh
  rw [hh]
  unfold polar
  rw [dotProduct_comm v.2 w.1]

theorem vectorLinearHom_preserves_polar (m : ℕ) (A : elementaryRootGroup K m)
    (v w : (Fin m → K) × (Fin m → K)) :
    polar (vectorLinearHom K m A v) (vectorLinearHom K m A w) = polar v w := by
  have hvec (u : (Fin m → K) × (Fin m → K)) :
      vectorEquiv K m (vectorLinearHom K m A u) =
        (A.val : Mat K m) *ᵥ vectorEquiv K m u := by
    rw [vectorLinearHom_apply, (vectorEquiv K m).apply_symm_apply]
  calc
    _ = pairing m (vectorEquiv K m (vectorLinearHom K m A v))
        (vectorEquiv K m (vectorLinearHom K m A w)) := (vectorEquiv_pairing K m _ _).symm
    _ = pairing m ((A.val : Mat K m) *ᵥ vectorEquiv K m v)
        ((A.val : Mat K m) *ᵥ vectorEquiv K m w) := by rw [hvec, hvec]
    _ = pairing m (vectorEquiv K m v) (vectorEquiv K m w) :=
      elementary_preserves_pairing m A _ _
    _ = _ := vectorEquiv_pairing K m v w

def pointLinearHom [Finite K] (hK : Nat.card K = 2) (m : ℕ) :
    elementaryRootGroup K m →* (CFSGSymplecticBinaryPointRadical.Coordinates K m ≃ₗ[K]
      CFSGSymplecticBinaryPointRadical.Coordinates K m) :=
  BinaryQuadraticLiftAction.liftHom hK (vectorLinearHom K m)
    (vectorLinearHom_preserves_polar K m)

theorem pointLinearHom_apply [Finite K] (hK : Nat.card K = 2) (m : ℕ)
    (A : elementaryRootGroup K m) (a : CFSGSymplecticBinaryPointRadical.Coordinates K m) :
    pointLinearHom K hK m A a =
      (vectorLinearHom K m A a.1,a.2+dotProduct a.1.1 a.1.2+
        dotProduct (vectorLinearHom K m A a.1).1 (vectorLinearHom K m A a.1).2) := rfl

theorem pointLinearHom_central [Finite K] (hK : Nat.card K = 2) (m : ℕ)
    (A : elementaryRootGroup K m) (c : K) : pointLinearHom K hK m A (0,c) = (0,c) :=
  BinaryQuadraticLiftAction.liftHom_central hK (vectorLinearHom K m)
    (vectorLinearHom_preserves_polar K m) A c

omit [CharP K 2] in
private theorem point_tail_transform (m : ℕ) (A : elementaryRootGroup K m)
    (v : (Fin m → K) × (Fin m → K)) :
    CFSGSymplecticBinaryPointRadical.tail K m (vectorLinearHom K m A v) =
      ((tailHom K m A).val : Mat K (m+1)) *ᵥ CFSGSymplecticBinaryPointRadical.tail K m v := by
  change tailExtend m (vectorEquiv K m (vectorLinearHom K m A v)) =
    ((tailHom K m A).val : Mat K (m+1)) *ᵥ tailExtend m (vectorEquiv K m v)
  rw [vectorLinearHom_apply, (vectorEquiv K m).apply_symm_apply]
  exact (tailHom_tailExtend K m A (vectorEquiv K m v)).symm

private theorem point_parameter_fixed [Finite K] (hK : Nat.card K = 2) (m : ℕ)
    (A : elementaryRootGroup K m) (a : CFSGSymplecticBinaryPointRadical.Coordinates K m) :
    CFSGSymplecticBinaryPointRadical.parameter K m (pointLinearHom K hK m A a) =
      CFSGSymplecticBinaryPointRadical.parameter K m a := by
  rw [pointLinearHom_apply]
  change (a.2+dotProduct a.1.1 a.1.2+
      dotProduct (vectorLinearHom K m A a.1).1 (vectorLinearHom K m A a.1).2)+
      dotProduct (vectorLinearHom K m A a.1).1 (vectorLinearHom K m A a.1).2 = _
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rfl

theorem tail_conjugation [Finite K] (hK : Nat.card K = 2) (m : ℕ) (hm : 0 < m)
    (A : elementaryRootGroup K m)
    (a : Multiplicative (CFSGSymplecticBinaryPointRadical.Coordinates K m)) :
    tailHom K m A * CFSGSymplecticBinaryPointRadical.elementaryHom K m hm a *
        (tailHom K m A)⁻¹ =
      CFSGSymplecticBinaryPointRadical.elementaryHom K m hm
        (Multiplicative.ofAdd (pointLinearHom K hK m A a.toAdd)) := by
  have he : ((tailHom K m A).val : Mat K (m+1)) *ᵥ
      CFSGSymplecticBinaryPointRadical.firstVector K m =
        CFSGSymplecticBinaryPointRadical.firstVector K m :=
    (tailHom_fixes_firstPair K m A).1
  have ho : pairing (m+1) (CFSGSymplecticBinaryPointRadical.firstVector K m)
      (CFSGSymplecticBinaryPointRadical.tail K m a.toAdd.1) = 0 :=
    tailVector_orthogonal_first (⟨a.toAdd.1.1,a.toAdd.1.2,0⟩ : Element K m)
  change tailHom K m A * shearElement K m hm (CFSGSymplecticBinaryPointRadical.firstVector K m)
      (CFSGSymplecticBinaryPointRadical.tail K m a.toAdd.1)
      (CFSGSymplecticBinaryPointRadical.parameter K m a.toAdd) * (tailHom K m A)⁻¹ = _
  rw [shearElement_conjugate m hm (tailHom K m A) _ _ _ he ho]
  change shearElement K m hm _ _ _ = shearElement K m hm _
    (CFSGSymplecticBinaryPointRadical.tail K m (pointLinearHom K hK m A a.toAdd).1)
    (CFSGSymplecticBinaryPointRadical.parameter K m (pointLinearHom K hK m A a.toAdd))
  rw [point_parameter_fixed, pointLinearHom_apply, point_tail_transform]

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointTailAction
