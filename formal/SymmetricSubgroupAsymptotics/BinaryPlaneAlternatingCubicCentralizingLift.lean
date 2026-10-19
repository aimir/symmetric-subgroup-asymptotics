import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalKlein

/-! Actual even block three-cycles admit centralizing lifts: squaring a
lift of the inverse cycle kills the actual cubic-kernel inversion
character. No order-three complement is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCubicCentralizingLift
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingCentralizerKleinLift (alpha)

private theorem automorphism_square {K : Type} [Group K] [Finite K]
    (e : K ≃* Cubic) (a : MulAut K) : a^2=1 := by
  have hh := RankOneCubicSylowCentralizer.automorphism_card_le_two e
  have hp : 0<Nat.card (MulAut K) := Nat.card_pos
  have hc : Nat.card (MulAut K)=1 ∨ Nat.card (MulAut K)=2 := by omega
  rcases hc with hc | hc
  · have ha : a=1 := by
      haveI : Subsingleton (MulAut K) := (Nat.card_eq_one_iff_unique.mp hc).1
      exact Subsingleton.elim _ _
    rw [ha,one_pow]
  · simpa only [hc] using (pow_card_eq_one' (x := a))

/-- The lift centralizes every element of the actual odd kernel. Its
cube has not been assumed trivial, and is not needed for normalization. -/
theorem exists_lift (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    (p : alternatingGroup (Fin 4)) (hp : p^3=1) :
    ∃ g : C, (g : Frame).right=p.val ∧
      ∀ o : oddKernel C, Commute g (o : C) := by
  obtain ⟨h,hh⟩ := heven (p^2)
  let g := h^2
  have ht : (g : Frame).right=p.val := by
    change PermutationalWreathProduct.rightHom ((h : Frame)^2)=p.val
    rw [map_pow]
    change (h : Frame).right^2=p.val
    rw [hh]
    change (((p^2)^2 : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))=p.val
    apply congrArg Subtype.val
    rw [← pow_mul,show (2*2 : ℕ)=3+1 by decide,pow_add,hp,pow_one,one_mul]
  have ha : alpha C g=1 := by
    change alpha C (h^2)=1
    rw [map_pow]
    exact automorphism_square e (alpha C h)
  refine ⟨g,ht,?_⟩
  intro o
  have ho := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
  change g*(o : C)*g⁻¹=(o : C) at ho
  exact mul_inv_eq_iff_eq_mul.mp ho

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCubicCentralizingLift
