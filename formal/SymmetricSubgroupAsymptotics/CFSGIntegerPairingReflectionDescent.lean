import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent
import SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections
import SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign

/-! A genuine norm-four/six reflection step: norm is preserved, height
strictly drops, and the new vector is nonnegative or has mixed signs.
This is an integer-lattice calculation, with no root-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerPairingReflectionDescent
open CFSGIntegerPairingPositiveDescent CFSGNormTwoLatticeReflections
open CFSGIntegerHeightSign
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem height_coordinate_step (x : I→ℤ) (i : I) (c : ℤ) :
    height (x-c • (Pi.single i (1:ℤ) : I→ℤ))=height x-c := by
  simp only [height,Pi.sub_apply,Pi.smul_apply,zsmul_eq_mul,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  simp [Pi.single_apply]

theorem reflection_step (B : LinearMap.BilinForm ℤ (I→ℤ))
    (hs : ∀x y,B x y=B y x)
    (hd : ∀i,B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (x : I→ℤ) (hx : ∀i,0≤x i) (hnorm : B x x=4 ∨ B x x=6) :
    ∃i : I,
      height (reflection B (Pi.single i (1:ℤ) : I→ℤ) x)<height x ∧
      B (reflection B (Pi.single i (1:ℤ) : I→ℤ) x)
        (reflection B (Pi.single i (1:ℤ) : I→ℤ) x)=B x x ∧
      ((∀j,0≤reflection B (Pi.single i (1:ℤ) : I→ℤ) x j) ∨
        ∃a b,0<reflection B (Pi.single i (1:ℤ) : I→ℤ) x a ∧
          reflection B (Pi.single i (1:ℤ) : I→ℤ) x b<0) := by
  classical
  have hn : 0<B x x := by rcases hnorm with h|h <;> omega
  obtain ⟨i,_,hci⟩ := exists_positive_coordinate_pairing B x hx hn
  let y := reflection B (Pi.single i (1:ℤ) : I→ℤ) x
  have hyheight : height y<height x := by
    change height (x-B x (Pi.single i (1:ℤ) : I→ℤ) •
      (Pi.single i (1:ℤ) : I→ℤ))<height x
    rw [height_coordinate_step]
    omega
  refine ⟨i,hyheight,norm_reflection B hs _ x (hd i),?_⟩
  change (∀j,0≤y j) ∨ ∃a b,0<y a ∧ y b<0
  by_cases hy : ∀j,0≤y j
  · exact Or.inl hy
  · obtain ⟨b,hb⟩ := not_forall.mp hy
    obtain ⟨a,hai,hxa⟩ := exists_positive_off_axis B x hx i (hd i) hnorm
    have hya : y a=x a := by
      change x a-(B x (Pi.single i (1:ℤ) : I→ℤ) •
        (Pi.single i (1:ℤ) : I→ℤ)) a=x a
      simp [Pi.smul_apply,Pi.single_apply,hai,Ne.symm hai]
    exact Or.inr ⟨a,b,by rwa [hya],lt_of_not_ge hb⟩

end SymmetricSubgroupAsymptotics.CFSGIntegerPairingReflectionDescent
