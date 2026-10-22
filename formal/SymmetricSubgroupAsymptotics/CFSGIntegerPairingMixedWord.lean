import SymmetricSubgroupAsymptotics.CFSGIntegerPairingReflectionDescent

/-! Explicit finite simple-reflection words carry nonnegative norm-four
or norm-six integer vectors to mixed signs. Strong height descent supplies
the word; no Weyl-orbit classification or root-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerPairingMixedWord
open CFSGNormTwoLatticeReflections CFSGIntegerHeightSign
open CFSGIntegerPairingReflectionDescent
variable {I : Type*} [Fintype I] [DecidableEq I]

def reflectionWord (B : LinearMap.BilinForm ℤ (I→ℤ)) : List I→(I→ℤ)→(I→ℤ)
  | [],x=>x
  | i::w,x=>reflectionWord B w (reflection B (Pi.single i (1:ℤ) : I→ℤ) x)

theorem exists_mixed_word (B : LinearMap.BilinForm ℤ (I→ℤ))
    (hs : ∀x y,B x y=B y x)
    (hd : ∀i,B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (x : I→ℤ) (hx : ∀i,0≤x i) (hnorm : B x x=4 ∨ B x x=6) :
    ∃(w : List I) (a b : I),0<reflectionWord B w x a ∧ reflectionWord B w x b<0 := by
  have H : ∀m : ℕ,∀y : I→ℤ,(height y).toNat=m→
      (∀i,0≤y i)→(B y y=4 ∨ B y y=6)→
      ∃(w : List I) (a b : I),0<reflectionWord B w y a ∧ reflectionWord B w y b<0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih=>
      intro y hym hy hnormy
      obtain ⟨i,hheight,hnormstep,hstep⟩ := reflection_step B hs hd y hy hnormy
      let z := reflection B (Pi.single i (1:ℤ) : I→ℤ) y
      change height z<height y at hheight
      change B z z=B y y at hnormstep
      change (∀j,0≤z j) ∨ ∃a b,0<z a ∧ z b<0 at hstep
      rcases hstep with hz|hz
      · have hzy : 0≤height z := Finset.sum_nonneg (fun j hj=>hz j)
        have hyy : 0≤height y := Finset.sum_nonneg (fun j hj=>hy j)
        have hlt : (height z).toNat<m := by omega
        have hnz : B z z=4 ∨ B z z=6 := by rw [hnormstep];exact hnormy
        obtain ⟨w,a,b,ha,hb⟩ := ih ((height z).toNat) hlt z rfl hz hnz
        exact ⟨i::w,a,b,ha,hb⟩
      · obtain ⟨a,b,ha,hb⟩ := hz
        exact ⟨[i],a,b,ha,hb⟩
  exact H ((height x).toNat) x rfl hx hnorm

end SymmetricSubgroupAsymptotics.CFSGIntegerPairingMixedWord
