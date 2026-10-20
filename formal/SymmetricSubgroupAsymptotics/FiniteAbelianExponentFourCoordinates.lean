import SymmetricSubgroupAsymptotics.C4SquareKernelCoordinates
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! Finite abelian exponent-four groups have one C4 coordinate per cyclic
invariant factor. The factor count is measured exactly by two-torsion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FiniteAbelianExponentFourCoordinates
open C4SquareKernelCoordinates

private def binaryIntoFour : C2 →* C4 where
  toFun x := Multiplicative.ofAdd (2*(x.toAdd.val : ZMod 4))
  map_one' := by decide +kernel
  map_mul' := by intro x y; revert x y; decide +kernel

private theorem binaryIntoFour_injective : Function.Injective binaryIntoFour := by
  intro x y
  revert x y
  decide +kernel

private def factorHom (n : ℕ) (hn : n=2 ∨ n=4) :
    Multiplicative (ZMod n) →* C4 := by
  classical
  by_cases h2 : n=2
  · subst n; exact binaryIntoFour
  · have h4 := hn.resolve_left h2
    subst n; exact MonoidHom.id _

private theorem factorHom_injective (n : ℕ) (hn : n=2 ∨ n=4) :
    Function.Injective (factorHom n hn) := by
  rcases hn with rfl | rfl
  · simpa [factorHom] using binaryIntoFour_injective
  · simpa [factorHom] using (Function.injective_id : Function.Injective (id : C4 → C4))

private def factorSquare (n : ℕ) (hn : n=2 ∨ n=4) :
    (powMonoidHom (α := Multiplicative (ZMod n)) 2).ker ≃ C2 := by
  classical
  by_cases h2 : n=2
  · subst n
    exact
      { toFun := Subtype.val
        invFun := fun x => ⟨x,by change x^2=1; revert x; decide +kernel⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · have h4 := hn.resolve_left h2
    subst n
    exact oneCoordinate

private def kernelCongr {G H : Type} [CommGroup G] [CommGroup H] (e : G ≃* H) :
    (powMonoidHom (α := G) 2).ker ≃ (powMonoidHom (α := H) 2).ker where
  toFun z := ⟨e z.val,by
    have hz : z.val^2=1 := z.property
    change (e z.val)^2=1
    rw [←map_pow,hz,map_one]⟩
  invFun z := ⟨e.symm z.val,by
    have hz : z.val^2=1 := z.property
    change (e.symm z.val)^2=1
    rw [←map_pow,hz,map_one]⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z.val)
  right_inv z := Subtype.ext (e.apply_symm_apply z.val)

private def productSquare {ι : Type} (n : ι → ℕ) (hn : ∀ i, n i=2 ∨ n i=4) :
    (powMonoidHom (α := (i : ι) → Multiplicative (ZMod (n i))) 2).ker ≃ (ι → C2) where
  toFun z i := factorSquare (n i) (hn i) ⟨z.val i,congrFun z.property i⟩
  invFun v := ⟨fun i => ((factorSquare (n i) (hn i)).symm (v i)).val,by
    funext i; exact ((factorSquare (n i) (hn i)).symm (v i)).property⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val
      ((factorSquare (n i) (hn i)).symm_apply_apply ⟨z.val i,congrFun z.property i⟩)
  right_inv v := by funext i; exact (factorSquare (n i) (hn i)).apply_symm_apply (v i)

private theorem factor_of_dvd_four (n : ℕ) (hgt : 1<n) (hd : n ∣ 4) : n=2 ∨ n=4 := by
  have hle : n≤4 := Nat.le_of_dvd (by decide) hd
  interval_cases n <;> omega

 theorem exists_coordinates (G : Type) [CommGroup G] [Finite G]
    (hfour : ∀ g : G, g^4=1) :
    ∃ r : ℕ, Nat.card (powMonoidHom (α := G) 2).ker=2^r ∧
      ∃ j : G →* (Fin r → C4), Function.Injective j := by
  classical
  obtain ⟨ι,inst,n,hn,⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  letI : Fintype ι := inst
  have hfactor (i : ι) : n i=2 ∨ n i=4 := by
    let v : (j : ι) → Multiplicative (ZMod (n j)) :=
      Function.update 1 i (Multiplicative.ofAdd 1)
    have hv : v^4=1 := by
      have hh := congrArg e (hfour (e.symm v))
      simpa only [map_pow,e.apply_symm_apply,map_one] using hh
    have hi := congrFun hv i
    have hi' : (4 : ZMod (n i))=0 := by
      simpa [v,toAdd_pow,nsmul_eq_mul] using congrArg Multiplicative.toAdd hi
    have hd : n i ∣ 4 := (ZMod.natCast_eq_zero_iff 4 (n i)).mp hi'
    exact factor_of_dvd_four (n i) (hn i) hd
  let k := (kernelCongr e).trans (productSquare n hfactor)
  have hk : Nat.card (powMonoidHom (α := G) 2).ker=2^(Fintype.card ι) := by
    have htwo : Nat.card C2=2 := by
      rw [Nat.card_congr Multiplicative.toAdd]
      simp
    rw [Nat.card_congr k,Nat.card_fun,htwo,Nat.card_eq_fintype_card]
  let j : G →* (Fin (Fintype.card ι) → C4) :=
    { toFun := fun g i => factorHom (n ((Fintype.equivFin ι).symm i))
        (hfactor _) (e g ((Fintype.equivFin ι).symm i))
      map_one' := by funext i; simp
      map_mul' := by intro g h; funext i; simp }
  refine ⟨Fintype.card ι,hk,j,?_⟩
  intro g h hgh
  apply e.injective
  funext i
  apply factorHom_injective (n i) (hfactor i)
  have hh := congrFun hgh ((Fintype.equivFin ι) i)
  change (factorHom (n ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i))) (hfactor _))
      (e g ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i))) =
    (factorHom (n ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i))) (hfactor _))
      (e h ((Fintype.equivFin ι).symm ((Fintype.equivFin ι) i))) at hh
  have hi : (Fintype.equivFin ι).symm ((Fintype.equivFin ι) i)=i :=
    (Fintype.equivFin ι).symm_apply_apply i
  rw [hi] at hh
  exact hh

end SymmetricSubgroupAsymptotics.FiniteAbelianExponentFourCoordinates
