import SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisPermutation

/-! An actual automorphism carrying one full coordinate axis onto
another carries every nonzero axis parameter to a nonzero parameter. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisParameters
open CFSGSimpleCoordinateAxes
variable {J K : Type*} [DecidableEq J] [AddCommGroup K]

theorem image_single_nonzero (F : MulAut (Multiplicative (J→K))) (i j : J)
    (hF : (axis (K:=K) i).map F.toMonoidHom=axis (K:=K) j)
    (a : K) (ha : a≠0) :
    ∃b : K,b≠0 ∧ F (Multiplicative.ofAdd (Pi.single i a : J→K))=
      Multiplicative.ofAdd (Pi.single j b : J→K) := by
  have hm : F (Multiplicative.ofAdd (Pi.single i a : J→K))∈axis (K:=K) j := by
    rw [←hF]
    exact ⟨_,single_mem_axis i a,rfl⟩
  obtain ⟨b,hb⟩ := (mem_axis_iff j _).mp hm
  refine ⟨b,?_,hb.symm⟩
  intro hz
  have hh : F (Multiplicative.ofAdd (Pi.single i a : J→K))=F 1 := by
    simpa [hz] using hb.symm
  have he := congrArg (fun c : Multiplicative (J→K)=>c.toAdd i) (F.injective hh)
  exact ha (by simpa [Pi.single_apply] using he)

end SymmetricSubgroupAsymptotics.CFSGSimpleCoordinateAxisParameters
