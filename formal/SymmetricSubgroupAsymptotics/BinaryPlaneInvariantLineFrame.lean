import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition

/-! A fixed nonzero vector of the actual local block stabilizer transports
to a global invariant line frame. The frame is built from actual block
transporters and preserves the literal local linear maps. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneInvariantLineFrame
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)

theorem exists_frame (C : Subgroup Frame)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (v0 : Plane) (hv0 : v0≠0)
    (hfixed : ∀ s : C, (s : Frame).right 0=0 → (s : Frame).left 0 v0=v0) :
    ∃ v : Fin 4 → Plane, (∀ i, v i≠0) ∧
      ∀ (g : C) (i : Fin 4),
        (g : Frame).left ((g : Frame).right i) (v i)=v ((g : Frame).right i) := by
  have htrans : ∀ i : Fin 4, ∃ h : C, (h : Frame).right 0=i := by
    intro i
    exact BinaryPlaneAlternatingKernelPartition.transitive C heven 0 i
  choose t ht using htrans
  let v : Fin 4 → Plane := fun i => (t i : Frame).left i v0
  refine ⟨v,?_,?_⟩
  · intro i hi
    apply hv0
    exact ((t i : Frame).left i).injective (hi.trans (map_zero _).symm)
  · intro g i
    let j := (g : Frame).right i
    let s : C := (t j)⁻¹*g*t i
    have htj : (t j : Frame).right⁻¹ j=0 := by
      have he := congrArg (t j : Frame).right.symm (ht j)
      simpa only [Equiv.symm_apply_apply] using he.symm
    have hs : (s : Frame).right 0=0 := by
      change ((((t j : Frame)⁻¹*(g : Frame))*(t i : Frame)).right) 0=0
      simp only [PermutationalWreathProduct.mul_right,PermutationalWreathProduct.inv_right,
        Equiv.Perm.mul_apply]
      rw [ht i]
      exact htj
    have hm : g*t i=t j*s := by
      dsimp only [s]
      rw [← mul_assoc,← mul_assoc,mul_inv_cancel,one_mul]
    have hg : (g : Frame).right⁻¹ j=i := (g : Frame).right.symm_apply_apply i
    have he := congrArg (fun z : C => (z : Frame).left j) hm
    simp only [Subgroup.coe_mul,PermutationalWreathProduct.mul_left,Pi.mul_apply] at he
    change (g : Frame).left j*(t i : Frame).left ((g : Frame).right⁻¹ j)=
      (t j : Frame).left j*(s : Frame).left ((t j : Frame).right⁻¹ j) at he
    rw [hg,htj] at he
    have hx := congrArg (fun L : Plane ≃ₗ[ZMod 2] Plane => L v0) he
    change (g : Frame).left j ((t i : Frame).left i v0)=
      (t j : Frame).left j ((s : Frame).left 0 v0) at hx
    rw [hfixed s hs] at hx
    exact hx

end SymmetricSubgroupAsymptotics.BinaryPlaneInvariantLineFrame
