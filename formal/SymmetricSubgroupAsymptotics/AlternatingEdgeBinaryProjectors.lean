import SymmetricSubgroupAsymptotics.SymmetricFourTwelvePointSocles
import SymmetricSubgroupAsymptotics.FourPointAlternatingGeneratorCover
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Finite operators on the six edges, followed by a symbolic invariant
subspace argument. No subspaces or normal subgroups are enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors
abbrev Vector := Fin 6 → ZMod 2
abbrev Plane := Fin 2 → ZMod 2

def rho : Representation (ZMod 2) (Equiv.Perm (Fin 4)) Vector :=
  (permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 6)) (Fin 6)).comp
    SymmetricFourTwelvePointSocles.edge
abbrev A : Module.End (ZMod 2) Vector := rho FourPointAlternatingGeneratorCover.a
def active : Module.End (ZMod 2) Vector := A+A^2

private abbrev project (i : Fin 6) : Vector →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i
private abbrev planeProject (i : Fin 2) : Plane →ₗ[ZMod 2] ZMod 2 := LinearMap.proj i

def constraints : Vector →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
  LinearMap.pi ![project 0 + project 5,
    project 1 + project 4,project 2 + project 3,
    project 0 + project 1 + project 2]
def W : Submodule (ZMod 2) Vector := constraints.ker
instance decidableMemW (v : Vector) : Decidable (v ∈ W) :=
  inferInstanceAs (Decidable (constraints v = 0))

def klein : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,Equiv.swap 0 3 * Equiv.swap 1 2]
def difference (d : Fin 3) : Module.End (ZMod 2) Vector := 1+rho (klein d)

private theorem reconstruct : ∀ v : Vector, v ∈ W →
    ![v 0,v 1,v 0+v 1,v 0+v 1,v 1,v 0] = v := by decide +kernel
private def embedding : Plane →ₗ[ZMod 2] Vector :=
  LinearMap.pi ![planeProject 0,planeProject 1,
    planeProject 0+planeProject 1,planeProject 0+planeProject 1,
    planeProject 1,planeProject 0]
private theorem embedding_mem : ∀ v : Plane, embedding v ∈ W := by decide +kernel

def planeEquiv : Plane ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofBijective (embedding.codRestrict W embedding_mem) (by
    constructor
    · intro v w h
      have h0 := congrArg (fun x : W => x.val 0) h
      have h1 := congrArg (fun x : W => x.val 1) h
      funext i
      fin_cases i
      · change v 0 = w 0 at h0
        exact h0
      · change v 1 = w 1 at h1
        exact h1
    · intro v
      refine ⟨![v.val 0,v.val 1],Subtype.ext ?_⟩
      funext i
      have hi := congrFun (reconstruct v.val v.property) i
      fin_cases i <;> exact hi)

theorem W_finrank : Module.finrank (ZMod 2) W = 2 := by
  rw [← planeEquiv.finrank_eq]
  simp

theorem active_difference_mem : ∀ (d : Fin 3) (v : Vector),
    active (difference d v) ∈ W := by decide +kernel
private theorem active_idempotent : ∀ v : Vector, active (active v) = active v := by decide +kernel
private theorem joint_kernel : ∀ v : Vector, active v = v →
    (∀ d : Fin 3, active (difference d v) = 0) → v ∈ W := by decide +kernel
private theorem nonzero_orbit : ∀ v w : Vector, v ∈ W → w ∈ W → v ≠ 0 → w ≠ 0 →
    w = v ∨ w = A v ∨ w = (A^2) v := by decide +kernel

theorem active_subspace_or_plane_le
    (K J : Submodule (ZMod 2) Vector)
    (hK : ∀ v ∈ K, A v ∈ K) (hJ : ∀ v ∈ J, A v ∈ J)
    (hcomm : ∀ v ∈ K, ∀ d : Fin 3, active (difference d v) ∈ J) :
    (∀ v ∈ K, active v ∈ W) ∨ W ≤ J := by
  classical
  by_cases h : ∀ v ∈ K, active v ∈ W
  · exact Or.inl h
  right
  push Not at h
  obtain ⟨v,hv,hvW⟩ := h
  have hav : active v ∈ K := K.add_mem (hK v hv) (hK (A v) (hK v hv))
  have hd : ∃ d : Fin 3, active (difference d (active v)) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hvW (joint_kernel (active v) (active_idempotent v) hn)
  obtain ⟨d,hd⟩ := hd
  let u := active (difference d (active v))
  have huJ : u ∈ J := hcomm (active v) hav d
  have huW : u ∈ W := active_difference_mem d (active v)
  intro w hw
  by_cases hw0 : w = 0
  · simpa only [hw0] using J.zero_mem
  rcases nonzero_orbit u w huW hw hd hw0 with he | he | he
  · rw [he]
    exact huJ
  · rw [he]
    exact hJ u huJ
  · rw [he]
    exact hJ (A u) (hJ u huJ)

end SymmetricSubgroupAsymptotics.AlternatingEdgeBinaryProjectors
