import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent

/-! A nonnegative lattice vector negatively paired with a norm-two
coordinate axis has a positive off-axis coordinate. Subtracting that
simple axis therefore gives a nonnegative or mixed-sign degree. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGIntegerNegativeSimpleStep
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem positive_off_axis_of_negative_pairing (B : LinearMap.BilinForm ℤ (I→ℤ))
    (x : I→ℤ) (hx : ∀j,0≤x j) (i : I)
    (hii : B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (hpair : B x (Pi.single i (1:ℤ) : I→ℤ)<0) : ∃j,j≠i ∧ 0<x j := by
  by_contra hn
  have haxis : x=x i • (Pi.single i (1:ℤ) : I→ℤ) := by
    funext j
    by_cases hji : j=i
    · subst j
      simp [Pi.smul_apply]
    · have hz : x j=0 := by
        have hn' : ¬0<x j := fun hp=>hn ⟨j,hji,hp⟩
        have := hx j
        omega
      simp [Pi.smul_apply,hji,hz]
  have heq : B x (Pi.single i (1:ℤ) : I→ℤ)=x i*2 := by
    calc
      _=B (x i • (Pi.single i (1:ℤ) : I→ℤ)) (Pi.single i (1:ℤ) : I→ℤ) :=
        congrArg (fun v : I→ℤ=>B v (Pi.single i (1:ℤ) : I→ℤ)) haxis
      _=_ := by rw [B.smul_left,hii]
  have := hx i
  omega

theorem sub_simple_nonnegative_or_mixed (B : LinearMap.BilinForm ℤ (I→ℤ))
    (x : I→ℤ) (hx : ∀j,0≤x j) (i : I)
    (hii : B (Pi.single i (1:ℤ) : I→ℤ) (Pi.single i (1:ℤ) : I→ℤ)=2)
    (hpair : B x (Pi.single i (1:ℤ) : I→ℤ)<0) :
    (∀j,0≤(x-(Pi.single i (1:ℤ) : I→ℤ)) j) ∨
      ∃a b,0<(x-(Pi.single i (1:ℤ) : I→ℤ)) a ∧
        (x-(Pi.single i (1:ℤ) : I→ℤ)) b<0 := by
  classical
  by_cases hy : ∀j,0≤(x-(Pi.single i (1:ℤ) : I→ℤ)) j
  · exact Or.inl hy
  · obtain ⟨b,hb⟩ := not_forall.mp hy
    obtain ⟨a,hai,ha⟩ := positive_off_axis_of_negative_pairing B x hx i hii hpair
    have hya : (x-(Pi.single i (1:ℤ) : I→ℤ)) a=x a := by
      simp [Pi.sub_apply,Pi.single_apply,hai,Ne.symm hai]
    exact Or.inr ⟨a,b,by rwa [hya],lt_of_not_ge hb⟩

end SymmetricSubgroupAsymptotics.CFSGIntegerNegativeSimpleStep
