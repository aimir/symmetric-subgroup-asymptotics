import SymmetricSubgroupAsymptotics.DiagonalScalarCodeDimensionBound
import SymmetricSubgroupAsymptotics.CoordinateSelfDualOrthogonalComplement
import SymmetricSubgroupAsymptotics.TernarySignedCoordinateSelfDual
import SymmetricSubgroupAsymptotics.ProperTransitiveMonomialScalarCode

/-! A nonzero proper invariant ternary submodule and the SAME sign
kernel have combined cardinal at most 54 for EVERY transitive signed
four-coordinate group. The sign code acts faithfully on both the module
and its genuine orthogonal subspace. Dimension bounds replace any list
of coordinate collision partitions or transitive permutation groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TernaryFourTransitiveProperKernelCapacity
open TernarySignedWreathLinearEquiv TernaryFourProperModuleSignKernel
open DiagonalInvariantSubmodules CoordinateSelfDualOrthogonalComplement

private def signCode (R : Subgroup Signed) :
    (topHom R).ker → (Fin 4 → (ZMod 3)ˣ) :=
  fun n i => coefficient (Fin 4) n.val.val i

private theorem signCode_injective (R : Subgroup Signed) :
    Function.Injective (signCode R) := by
  intro n m he
  apply Subtype.ext
  apply Subtype.ext
  apply PermutationalWreathProduct.ext
  · funext i
    apply OddMarkerTernaryChart.signUnitHom_injective
    exact congrFun he i
  · exact (show n.val.val.right=1 from n.property).trans
      (show m.val.val.right=1 from m.property).symm

private theorem code_preserves (R : Subgroup Signed)
    (W : Submodule (ZMod 3) (Fin 4 → ZMod 3))
    (hW : ∀ (g : R) w,w∈W → linearHom (Fin 4) g.val w∈W)
    (n : (topHom R).ker) (w : Fin 4 → ZMod 3) (hw : w∈W) :
    (fun i => (signCode R n i : ZMod 3)*w i)∈W := by
  have hn : permutationHom (Fin 4) n.val.val=1 := n.property
  have he : linearHom (Fin 4) n.val.val w=
      (fun i => (signCode R n i : ZMod 3)*w i) := by
    funext i
    have hid : (1 : Equiv.Perm (Fin 4)).symm=1 := rfl
    simp only [linearHom_apply,hn,hid,Equiv.Perm.one_apply,signCode]
  rw [←he]
  exact hW n.val w hw

private theorem full_coordinates (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (W : Submodule (ZMod 3) (Fin 4 → ZMod 3)) (hne : W≠⊥)
    (hW : ∀ (g : R) w,w∈W → linearHom (Fin 4) g.val w∈W) :
    FullCoordinates W := by
  have hnonzero := ProperTransitiveMonomialScalarCode.coordinate_nonzero_of_transitive_monomial
    ((linearHom (Fin 4)).comp R.subtype) (topHom R)
    (fun g i => coefficient (Fin 4) g.val i)
    (fun g w i => linearHom_apply (Fin 4) g.val w i) htrans W hne hW
  intro i c
  obtain ⟨w,hw⟩ := hnonzero i
  refine ⟨(c*(w.val i)⁻¹) • w,?_⟩
  change (c*(w.val i)⁻¹)*w.val i=c
  rw [mul_assoc,inv_mul_cancel₀ hw,mul_one]

private theorem kernel_card_le_two_pow_finrank (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (W : Submodule (ZMod 3) (Fin 4 → ZMod 3)) (hne : W≠⊥)
    (hW : ∀ (g : R) w,w∈W → linearHom (Fin 4) g.val w∈W) :
    Nat.card (topHom R).ker≤2^Module.finrank (ZMod 3) W := by
  have hunits : Nat.card (ZMod 3)ˣ=2 :=
    (Nat.card_congr OddMarkerTernaryChart.signScalarEquiv.symm.toEquiv).trans
      ((Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)).trans
        (Nat.card_zmod 2))
  have h := DiagonalScalarCodeDimensionBound.code_card_le_units_pow_finrank
    (signCode R) (signCode_injective R) W (code_preserves R W hW)
    (full_coordinates R htrans W hne hW)
  simpa only [hunits] using h

theorem module_card_mul_sign_kernel_card_le_fiftyFour
    (R : Subgroup Signed)
    (htrans : ∀ i j : Fin 4,∃g : R,topHom R g i=j)
    (W : Submodule (ZMod 3) (Fin 4 → ZMod 3)) (hne : W≠⊥) (hproper : W≠⊤)
    (hW : ∀ (g : R) w,w∈W → linearHom (Fin 4) g.val w∈W) :
    Nat.card W*Nat.card (topHom R).ker≤54 := by
  let C := orthogonal W
  have hCne : C≠⊥ := orthogonal_ne_bot_of_proper W hproper
  have hC : ∀ (g : R) w,w∈C → linearHom (Fin 4) g.val w∈C :=
    invariant ((linearHom (Fin 4)).comp R.subtype)
      (TernarySignedCoordinateSelfDual.coordinateDualEquiv_intertwines_subgroup R) W hW
  have hEW := kernel_card_le_two_pow_finrank R htrans W hne hW
  have hEC := kernel_card_le_two_pow_finrank R htrans C hCne hC
  have hsum : Module.finrank (ZMod 3) W+Module.finrank (ZMod 3) C=4 :=
    finrank_add_orthogonal W
  have hposW : 0<Module.finrank (ZMod 3) W := Nat.pos_of_ne_zero
    (fun h => hne (Submodule.finrank_eq_zero.mp h))
  have hposC : 0<Module.finrank (ZMod 3) C := Nat.pos_of_ne_zero
    (fun h => hCne (Submodule.finrank_eq_zero.mp h))
  have hcard : Nat.card W=3^Module.finrank (ZMod 3) W := by
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K:=ZMod 3) (V:=W))
  have hcases : Module.finrank (ZMod 3) W=1 ∨
      Module.finrank (ZMod 3) W=2 ∨ Module.finrank (ZMod 3) W=3 := by omega
  rcases hcases with hd|hd|hd
  · have hE : Nat.card (topHom R).ker≤2 := by simpa only [hd] using hEW
    rw [hcard,hd]
    nlinarith
  · have hE : Nat.card (topHom R).ker≤4 := by simpa only [hd] using hEW
    rw [hcard,hd]
    nlinarith
  · have hc : Module.finrank (ZMod 3) C=1 := by omega
    have hE : Nat.card (topHom R).ker≤2 := by simpa only [hc] using hEC
    rw [hcard,hd]
    nlinarith

end SymmetricSubgroupAsymptotics.TernaryFourTransitiveProperKernelCapacity
