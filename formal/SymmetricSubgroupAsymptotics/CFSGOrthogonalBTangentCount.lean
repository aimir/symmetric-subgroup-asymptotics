import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateTangentCount
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGIsometryTangentTransport
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Every original nonzero singular vector has the same exact tangent
count, by the previously proved actual root-word normalization. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates
open CFSGOrthogonalBTailCoordinates CFSGOrthogonalBUnipotent
open CFSGIsometryTangentTransport
variable (K : Type) [Field K] [Finite K]

def naturalLinearEquiv (n:ℕ) (g:elementaryRootGroup K n) :
    (Index n→K) ≃ₗ[K] (Index n→K) :=
  (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Index n→K))) g.val

def firstTangentEquiv (n:ℕ) (h2:(2:K)≠0) :
    Tangent (gram K (n+1)).toBilin' (Pi.single (pos (n+1) 0) 1) ≃
      {v:Index (n+1)→K //(gram K (n+1)).toBilin' v v=0 ∧ v (neg (n+1) 0)=0} :=
  Equiv.subtypeEquivRight (fun v=>by
    constructor
    · rintro ⟨hn,hp⟩
      refine ⟨hn,?_⟩
      rw [pairing_first_positive] at hp
      exact (mul_eq_zero.mp hp).resolve_left h2
    · rintro ⟨hn,hp⟩
      refine ⟨hn,?_⟩
      rw [pairing_first_positive,hp,mul_zero])

theorem tangent_card (h2:(2:K)≠0) (s:ℕ) (v:Index (s+2)→K)
    (hv:v≠0) (hs:(gram K (s+2)).toBilin' v v=0) :
    Nat.card (Tangent (gram K (s+2)).toBilin' v)=Nat.card K^(2*(s+2)-1) := by
  obtain ⟨g,hg⟩:=exists_normalize_singular K h2 s v hv hs
  let e:=naturalLinearEquiv K (s+2) g
  have he:∀x y,(gram K (s+2)).toBilin' (e x) (e y)=(gram K (s+2)).toBilin' x y := by
    intro x y
    exact natural_pairing_invariant h2 (s+2) g x y
  have hgv:e v=Pi.single (pos (s+2) 0) 1 := hg
  have hcard:=Nat.card_congr (tangentEquiv (gram K (s+2)).toBilin' e he v)
  rw [hgv] at hcard
  calc
    Nat.card (Tangent (gram K (s+2)).toBilin' v)=
        Nat.card (Tangent (gram K (s+2)).toBilin' (Pi.single (pos (s+2) 0) 1)):=hcard
    _=Nat.card {w:Index (s+2)→K //(gram K (s+2)).toBilin' w w=0 ∧ w (neg (s+2) 0)=0}:=
      Nat.card_congr (firstTangentEquiv K (s+1) h2)
    _=Nat.card K^(2*(s+1)+1):=coordinate_tangent_card K (s+1) h2
    _=Nat.card K^(2*(s+2)-1):=by congr 1 <;> omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorCount
