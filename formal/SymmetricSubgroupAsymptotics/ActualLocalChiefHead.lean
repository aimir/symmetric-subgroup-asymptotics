import SymmetricSubgroupAsymptotics.ActualLocalChiefSteps

/-! The actual local-chief recurrence. Every local factor and every
ambient intersection is constructed from the original evaluation. The
ternary width coefficient is proved for the original induced quotient;
no published prime-power module hypothesis is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Finite A] [Group R] [Finite R]
variable (N H : Subgroup A) [N.Normal] (θ : N→*R) (β : H→*R)
variable (hθ : ∀ (h:H) (n:N),θ (MulAut.conjNormal (h:A) n)=β h*θ n*(β h)⁻¹)
variable (hβ : Function.Surjective β)
variable (hsep:∀n:N,(∀a:A,θ (MulAut.conjNormal a n)=1)→n=1)
include hθ hβ hsep

theorem actualLocalChiefHead_bound
    (s:ActualChiefSeries R) :
    (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ)≤
      (actualChiefSeriesTernaryWeight s:ℝ)*(ternaryIndexWidth H.index:ℝ) := by
  let C (i:Fin (s.length+1)) := localChiefIntersection N θ (s.subgroup i)
  let d (i:Fin (s.length+1)) : ℝ :=
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 (C i))
  let w (i:Fin s.length) : ℝ :=
    chiefTernaryWeight (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  have hs (i:Fin s.length) :
      d i.succ≤w i*(ternaryIndexWidth H.index:ℝ)+d i.castSucc :=
    ternaryChiefStep_le _ _ H _
      (actualLocalChiefStep N H θ β hθ hβ _ _ (s.step i).le (s.chief i))
  have hsum := Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset (Fin s.length)))=>hs i)
  have hz : C 0=⊥ := by
    dsimp [C]
    rw [s.head]
    exact localChiefIntersection_bot N θ hsep
  have hdz : d 0=0 := by
    haveI : Subsingleton (C 0) := by rw [hz]; infer_instance
    change (Module.finrank (ZMod 3) (primeRelativeCharacters 3 (C 0)):ℝ)=0
    exact_mod_cast (primeRelativeHead_perfect 3 (C 0))
  have hlast : C (Fin.last s.length)=N := by
    dsimp [C]
    rw [s.last,localChiefIntersection_top]
  have htel : d 0+(∑i:Fin s.length,d i.succ)=
      (∑i:Fin s.length,d i.castSucc)+d (Fin.last s.length) := by
    exact (Fin.sum_univ_succ d).symm.trans (Fin.sum_univ_castSucc d)
  rw [hdz,zero_add] at htel
  simp only [Finset.sum_add_distrib,←Finset.sum_mul] at hsum
  have hw : (∑i:Fin s.length,w i)=(actualChiefSeriesTernaryWeight s:ℝ) := by
    simp only [actualChiefSeriesTernaryWeight,Nat.cast_sum,w]
  rw [hw] at hsum
  have he : d (Fin.last s.length)=
      (Module.finrank (ZMod 3) (primeRelativeCharacters 3 N):ℝ) := by
    have heq (B D:Subgroup A) [B.Normal] [D.Normal] (he:B=D) :
        Module.finrank (ZMod 3) (primeRelativeCharacters 3 B)=
          Module.finrank (ZMod 3) (primeRelativeCharacters 3 D) := by
      subst D
      rfl
    exact congrArg (Nat.cast:ℕ→ℝ) (heq (C (Fin.last s.length)) N hlast)
  rw [he] at htel
  linarith

end SymmetricSubgroupAsymptotics
