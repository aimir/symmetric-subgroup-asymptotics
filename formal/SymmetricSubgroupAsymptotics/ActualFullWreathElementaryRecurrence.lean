import SymmetricSubgroupAsymptotics.ActualFullWreathElementaryFibreCount
import SymmetricSubgroupAsymptotics.ActualFullWreathFamilyFibreSum

/-! The actual abelian local-chief recurrence for the ENTIRE family.
The multiplier is computed from the closed induced capacity and the
CFSG-only weak transitive rank bound; no finite-image census is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathElementaryRecurrence
open ActualFullWreathFamily ActualFullWreathPreimage ActualFullWreathElementaryFibreCount

def exponentCeiling (a s t : ℕ) (c : ℝ) : ℕ :=
  Nat.ceil ((a : ℝ)*t/Real.sqrt (Real.logb 2 (t : ℝ))+
    c*WeakTransitiveDegreeInduction.rate (s*t))

variable {R R' Q I : Type} [Group R] [Finite R] [Group R'] [Finite R']
    [Group Q] [Finite Q] [Fintype I] [Nonempty I] [MulAction Q I]
    [FaithfulSMul Q I] [MulAction.IsPretransitive Q I]
    (phi : R →* R') (hphi : Function.Surjective phi)
    (C : ElementaryMinimalNormalChart phi.ker)

include hphi in
theorem card_le_quotient_mul
    (c : ℝ)
    (hbudget : ∀ n : ℕ,2≤n → ∀ J : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive J (Fin n) →
        (MarkedC4.genRank J : ℝ)≤c*WeakTransitiveDegreeInduction.rate n)
    (hI : 2≤Nat.card I) :
    Nat.card (Family R Q I)≤Nat.card (Family R' Q I)*
      (Nat.card phi.ker)^(Nat.card I *
        exponentCeiling (Module.finrank (ZMod C.p) C.V) (Nat.card R') (Nat.card I) c) := by
  apply ActualFullWreathFamilyFibreSum.card_le_mul phi hphi
  intro H
  let i : I := Classical.choice inferInstance
  have hcap := capacity_le_root_log phi hphi H C i
    (by simpa only [Fintype.card_eq_nat_card] using hI)
  simp only [Fintype.card_eq_nat_card] at hcap
  have hd := quotient_rank_le_of_uniform phi hphi H c hbudget hI
  have hs : ((capacity phi hphi H C i+
      MarkedC4.genRank ((preimageState phi hphi H).A ⧸ layerKernel phi hphi H) : ℕ) : ℝ)≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*Nat.card I /
        Real.sqrt (Real.logb 2 (Nat.card I : ℝ))+
          c*WeakTransitiveDegreeInduction.rate (Nat.card R'*Nat.card I) := by
    simpa only [Nat.cast_add] using add_le_add hcap hd
  have hnat : capacity phi hphi H C i+
      MarkedC4.genRank ((preimageState phi hphi H).A ⧸ layerKernel phi hphi H)≤
      exponentCeiling (Module.finrank (ZMod C.p) C.V) (Nat.card R') (Nat.card I) c := by
    have hh := hs.trans (Nat.le_ceil _)
    exact Nat.cast_le.mp hh
  exact (card_fibre_le phi hphi H C i).trans
    (Nat.pow_le_pow_right Nat.card_pos (Nat.mul_le_mul_left _ hnat))

include hphi in
theorem exists_cfsg_recurrence (hCFSG : CFSG.CFSGClassification) (hI : 2≤Nat.card I) :
    ∃ c : ℝ,1≤c ∧ Nat.card (Family R Q I)≤Nat.card (Family R' Q I)*
      (Nat.card phi.ker)^(Nat.card I *
        exponentCeiling (Module.finrank (ZMod C.p) C.V) (Nat.card R') (Nat.card I) c) := by
  obtain ⟨c,hc,hbudget⟩ := CFSGWeakTransitiveGeneratorBound.exists_uniform_generator_budget hCFSG
  exact ⟨c,hc,card_le_quotient_mul phi hphi C c hbudget hI⟩

end SymmetricSubgroupAsymptotics.ActualFullWreathElementaryRecurrence
