import SymmetricSubgroupAsymptotics.CFSGTypeASLTwoGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeATwistedCycleGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeAPrimeFieldCycleGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeACyclicCoordinates
import Mathlib.Algebra.CharP.CharAndCard

/-! Uniform two-generation for the literal matrix type-A family. The
rank-one case uses its separate Weyl identity; dimensions at least three
use a signed coordinate cycle. Fields of order two or three are handled
by the uniform prime-field root-one argument, without a finite census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldGeneration
open CFSGTypeAElementaryMatrices CFSGTypeAMonomialMatrices
open CFSGTypeACyclicCoordinates CFSGTypeARootTorus
variable {F : Type*} [Field F] [Finite F]

theorem exists_generating_pair_of_four (m : ℕ) (hm : 3≤m) (hcard : 4≤Nat.card F) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin m) F,
      Subgroup.closure ({x,y} : Set (Matrix.SpecialLinearGroup (Fin m) F))=⊤ := by
  let i : Fin m := ⟨0,by omega⟩
  let σ := finRotate m
  have hσ : σ.IsCycleOn (Finset.univ : Finset (Fin m)) := finRotate_cycle m (by omega)
  have hi : i≠σ.symm i := predecessor_ne (by simpa using (show 2≤m by omega)) σ hσ i
  let W : Matrix.SpecialLinearGroup (Fin m) F := signedPermutation i σ
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Fˣ)
  let x := torus hi g
  let y := elementary hi 1*W
  refine ⟨x,y,CFSGTypeATwistedCycleGeneration.eq_top_of_twisted_cycle
    (by simpa using hm) hcard σ hσ W (weights i σ) rfl (weights_ne_zero i σ)
    i g hg hi _ ?_ ?_⟩
  · exact Subgroup.subset_closure (by simp [x])
  · exact Subgroup.subset_closure (by simp [y])

theorem exists_generating_pair_prime (m : ℕ) (hm : 2≤m) (p : ℕ)
    [CharP F p] (hcard : Nat.card F=p) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin m) F,
      Subgroup.closure ({x,y} : Set (Matrix.SpecialLinearGroup (Fin m) F))=⊤ := by
  let i : Fin m := ⟨0,by omega⟩
  let σ := finRotate m
  have hσ : σ.IsCycleOn (Finset.univ : Finset (Fin m)) := finRotate_cycle m hm
  have hi : i≠σ.symm i := predecessor_ne (by simpa using hm) σ hσ i
  let W : Matrix.SpecialLinearGroup (Fin m) F := signedPermutation i σ
  let x := elementary hi (1 : F)
  refine ⟨x,W,CFSGTypeAPrimeFieldCycleGeneration.eq_top_of_prime_field_edge p hcard
    (by simpa using hm) σ hσ W (weights i σ) rfl (weights_ne_zero i σ)
    _ ?_ i hi ?_⟩
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp [x])

/-- The exact small-parameter guard is only needed in dimension two. -/
theorem exists_generating_pair (m : ℕ) (hm : 2≤m)
    (hsmall : m=2→4≤Nat.card F) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin m) F,
      Subgroup.closure ({x,y} : Set (Matrix.SpecialLinearGroup (Fin m) F))=⊤ := by
  by_cases he : m=2
  · subst m
    exact CFSGTypeASLTwoGeneration.exists_generating_pair (hsmall rfl)
  have hm3 : 3≤m := by omega
  by_cases hc : 4≤Nat.card F
  · exact exists_generating_pair_of_four m hm3 hc
  letI : Fintype F := Fintype.ofFinite F
  have hlo : 1<Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hp : (Nat.card F).Prime := by
    have hh : Nat.card F=2∨Nat.card F=3 := by omega
    rcases hh with hh|hh <;> rw [hh] <;> decide
  letI : Fact (Nat.card F).Prime := ⟨hp⟩
  letI : CharP F (Nat.card F) := charP_of_card_eq_prime (by rw [Nat.card_eq_fintype_card])
  exact exists_generating_pair_prime m hm (Nat.card F) rfl

theorem genRank_le_two (m : ℕ) (hm : 2≤m) (hsmall : m=2→4≤Nat.card F) :
    MarkedC4.genRank (Matrix.SpecialLinearGroup (Fin m) F)≤2 := by
  obtain ⟨x,y,hxy⟩ := exists_generating_pair m hm hsmall
  have hc : Subgroup.closure
      (({x,y} : Finset (Matrix.SpecialLinearGroup (Fin m) F)) : Set (Matrix.SpecialLinearGroup (Fin m) F))=⊤ := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

/-- The quotient is the original literal PSL matrix model. -/
theorem psl_exists_generating_pair (m : ℕ) (hm : 2≤m) (hsmall : m=2→4≤Nat.card F) :
    ∃ x y : Matrix.ProjectiveSpecialLinearGroup (Fin m) F,
      Subgroup.closure ({x,y} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin m) F))=⊤ := by
  obtain ⟨x,y,hxy⟩ := exists_generating_pair m hm hsmall
  let q := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F))
  refine ⟨q x,q y,?_⟩
  have he := congrArg (Subgroup.map q) hxy
  simpa only [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using he

theorem psl_genRank_le_two (m : ℕ) (hm : 2≤m) (hsmall : m=2→4≤Nat.card F) :
    MarkedC4.genRank (Matrix.ProjectiveSpecialLinearGroup (Fin m) F)≤2 := by
  obtain ⟨x,y,hxy⟩ := psl_exists_generating_pair m hm hsmall
  have hc : Subgroup.closure
      (({x,y} : Finset (Matrix.ProjectiveSpecialLinearGroup (Fin m) F)) : Set (Matrix.ProjectiveSpecialLinearGroup (Fin m) F))=⊤ := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hxy
  exact (MarkedC4.genRank_le hc).trans Finset.card_le_two

end SymmetricSubgroupAsymptotics.CFSGTypeAFiniteFieldGeneration
