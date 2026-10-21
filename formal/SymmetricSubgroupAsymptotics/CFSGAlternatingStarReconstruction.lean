import SymmetricSubgroupAsymptotics.CFSGAlternatingStarRelations

/-! Point reconstruction from actual images of a star of 3-cycles.
The bijection retains all original point labels. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingStarReconstruction
open Equiv Equiv.Perm CFSGAlternatingStarGenerators CFSGAlternatingStarRelations
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Compatible, distinct images of the star generators determine an
actual permutation of the original point set. -/
theorem exists_point_conjugator (a b A B : α) (hab : a≠b) (hAB : A≠B)
    (F : α→Perm α)
    (hform : ∀ i,i≠a→i≠b→∃ c,c≠A ∧ c≠B ∧ F i=cycle A B c)
    (hinj : ∀ i j,i≠a→i≠b→j≠a→j≠b→F i=F j→i=j) :
    ∃ σ : Perm α,σ a=A ∧ σ b=B ∧
      ∀ i,i≠a→i≠b→F i=σ*cycle a b i*σ⁻¹ := by
  let δ : α→α := fun i => F i B
  have hd : ∀ i,i≠a→i≠b→δ i≠A ∧ δ i≠B ∧ F i=cycle A B (δ i) := by
    intro i hia hib
    obtain ⟨c,hcA,hcB,hc⟩ := hform i hia hib
    have he : δ i=c := by
      dsimp [δ]
      rw [hc]
      simp only [cycle,Perm.mul_apply,swap_apply_def]
      grind
    simpa only [he] using And.intro hcA (And.intro hcB hc)
  have hdi : ∀ i j,i≠a→i≠b→j≠a→j≠b→δ i=δ j→i=j := by
    intro i j hia hib hja hjb he
    apply hinj i j hia hib hja hjb
    rw [(hd i hia hib).2.2,(hd j hja hjb).2.2,he]
  let φ : α→α := fun i => if i=a then A else if i=b then B else δ i
  have hφa : φ a=A := by simp [φ]
  have hφb : φ b=B := by simp [φ,Ne.symm hab]
  have hφd : ∀ i,i≠a→i≠b→φ i=δ i := by
    intro i hia hib
    simp only [φ,if_neg hia,if_neg hib]
  have hφ : Function.Injective φ := by
    intro i j he
    by_cases hia : i=a
    · by_cases hja : j=a
      · exact hia.trans hja.symm
      by_cases hjb : j=b
      · rw [hia,hφa,hjb,hφb] at he
        exact False.elim (hAB he)
      rw [hia,hφa,hφd j hja hjb] at he
      exact False.elim ((hd j hja hjb).1 he.symm)
    by_cases hib : i=b
    · by_cases hja : j=a
      · rw [hib,hφb,hja,hφa] at he
        exact False.elim (hAB he.symm)
      by_cases hjb : j=b
      · exact hib.trans hjb.symm
      rw [hib,hφb,hφd j hja hjb] at he
      exact False.elim ((hd j hja hjb).2.1 he.symm)
    by_cases hja : j=a
    · rw [hφd i hia hib,hja,hφa] at he
      exact False.elim ((hd i hia hib).1 he)
    by_cases hjb : j=b
    · rw [hφd i hia hib,hjb,hφb] at he
      exact False.elim ((hd i hia hib).2.1 he)
    rw [hφd i hia hib,hφd j hja hjb] at he
    exact hdi i j hia hib hja hjb he
  let σ : Perm α := Equiv.ofBijective φ ⟨hφ,Finite.surjective_of_injective hφ⟩
  have hσa : σ a=A := by simp [σ,φ]
  have hσb : σ b=B := by simp [σ,φ,Ne.symm hab]
  refine ⟨σ,hσa,hσb,?_⟩
  intro i hia hib
  have hσi : σ i=δ i := by simp [σ,φ,hia,hib]
  rw [cycle_conjugation,hσa,hσb,hσi]
  exact (hd i hia hib).2.2

end SymmetricSubgroupAsymptotics.CFSGAlternatingStarReconstruction
