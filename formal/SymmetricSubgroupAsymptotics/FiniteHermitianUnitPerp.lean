import SymmetricSubgroupAsymptotics.FiniteHermitianUnitVectorSection
import SymmetricSubgroupAsymptotics.CFSGHermitianMaximalExchange

/-! A unit vector splits each actual nondegenerate subspace into its
line and the orthogonal kernel inside that SAME subspace. These lemmas
retain the literal ambient pairing and provide the recursive geometric
step toward an orthonormal basis. No order bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerp
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan

variable {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)

def unitPerp (W : Submodule K (I → K)) (v : I → K) : Submodule K (I → K) :=
  W ⊓ (pairRightLinear sigma H v).ker

theorem exists_decomposition (W : Submodule K (I → K)) (v : I → K)
    (hv : v ∈ W) (hone : hermitianPair sigma H v v=1)
    (x : I → K) (hx : x ∈ W) :
    ∃ a : K, ∃ p ∈ unitPerp sigma H W v, a • v+p=x := by
  let a := hermitianPair sigma H v x
  let p := x-a • v
  have hp : p ∈ unitPerp sigma H W v := by
    refine ⟨W.sub_mem hx (W.smul_mem a hv),?_⟩
    change (pairRightLinear sigma H v) (x-a • v)=0
    rw [map_sub,map_smul]
    change hermitianPair sigma H v x-a*hermitianPair sigma H v v=0
    rw [hone,mul_one]
    exact sub_self a
  refine ⟨a,p,hp,?_⟩
  calc
    a • v+p=p+a • v := add_comm _ _
    _ = x := sub_add_cancel x (a • v)

theorem nondegenerate_unitPerp (W : Submodule K (I → K)) (v : I → K)
    (hv : v ∈ W) (hone : hermitianPair sigma H v v=1)
    (hswap : ∀ x y, hermitianPair sigma H x y=0 ↔ hermitianPair sigma H y x=0)
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y=0) → x=0) :
    ∀ x ∈ unitPerp sigma H W v,
      (∀ y ∈ unitPerp sigma H W v, hermitianPair sigma H x y=0) → x=0 := by
  intro x hx hzero
  apply hND x hx.1
  intro y hy
  obtain ⟨a,p,hp,he⟩ := exists_decomposition sigma H W v hv hone y hy
  rw [←he,hermitianPair_add_right,hzero p hp,add_zero]
  have horth : hermitianPair sigma H x v=0 := (hswap v x).mp hx.2
  have hh := hermitianPair_smul sigma H 1 a x v
  simpa only [one_smul,map_one,one_mul,horth,mul_zero] using hh

end SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerp
