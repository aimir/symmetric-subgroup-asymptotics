import SymmetricSubgroupAsymptotics.FiniteCyclicProductDegreeBudget
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.Algebra.Group.Pi.Lemmas

/-! A noncyclic abelian group of order8 or9 acts faithfully on at most six
points. The existing finite-abelian structure theorem supplies its actual
cyclic factors; disjoint regular coordinate actions cost the sum, not the
product, of their orders. No explicit model classification is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Coordinatewise regular permutations on the original disjoint union. -/
def productCoordinateRegularPermutations {I : Type} (A : I→Type) [∀ i,Group (A i)] :
    (∀ i,A i)→*(∀ i,Equiv.Perm (A i)) where
  toFun g i := MulAction.toPermHom (A i) (A i) (g i)
  map_one' := funext fun i => (MulAction.toPermHom (A i) (A i)).map_one
  map_mul' g h := funext fun i => (MulAction.toPermHom (A i) (A i)).map_mul (g i) (h i)

def productDisjointRegularAction {I : Type} (A : I→Type) [∀ i,Group (A i)] :
    (∀ i,A i)→*Equiv.Perm (Σ i,A i) :=
  (Equiv.Perm.sigmaCongrRightHom A).comp (productCoordinateRegularPermutations A)

theorem productDisjointRegularAction_injective {I : Type} (A : I→Type) [∀ i,Group (A i)] :
    Function.Injective (productDisjointRegularAction A) := by
  intro g h hgh
  have he : productCoordinateRegularPermutations A g=productCoordinateRegularPermutations A h :=
    Equiv.Perm.sigmaCongrRightHom_injective hgh
  funext i
  apply (show Function.Injective (MulAction.toPermHom (A i) (A i)) from MulAction.toPerm_injective)
  exact congrFun he i

private theorem cyclicProduct_isCyclic_of_card_le_one
    {I : Type} [Fintype I] (A : I→Type) [∀ i,Group (A i)] [∀ i,IsCyclic (A i)]
    (hI : Fintype.card I≤1) : IsCyclic (∀ i,A i) := by
  letI : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hI
  by_cases hi : Nonempty I
  · let i : I := Classical.choice hi
    let f := Pi.evalMonoidHom A i
    have hf : Function.Bijective f := by
      constructor
      · intro g h he
        funext j
        have hj : j=i := Subsingleton.elim _ _
        subst j
        exact he
      · intro a
        exact ⟨Pi.mulSingle i a,Pi.mulSingle_eq_same i a⟩
    let e := MulEquiv.ofBijective f hf
    exact isCyclic_of_surjective e.symm e.symm.surjective
  · letI : IsEmpty I := not_nonempty_iff.mp hi
    infer_instance

/-- Every point and every group element stays tied to its actual cyclic
coordinate. Cyclic exceptions are left for the linear-character route. -/
theorem smallAbelian_noncyclic_faithful_permutation_six
    {G : Type} [CommGroup G] [Finite G]
    (hG : Nat.card G=8 ∨ Nat.card G=9) (hnc : ¬IsCyclic G) :
    ∃ d : ℕ,0<d ∧ d≤6 ∧
      ∃ f : G→*Equiv.Perm (Fin d),Function.Injective f := by
  obtain ⟨I,inst,n,hn,⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  letI : Fintype I := inst
  letI (i : I) : NeZero (n i) := ⟨by have hi:=hn i;omega⟩
  let A : I→Type := fun i => Multiplicative (ZMod (n i))
  have hI : 2≤Fintype.card I := by
    by_contra h
    have hs : Fintype.card I≤1 := by omega
    letI : IsCyclic (∀ i,A i) := cyclicProduct_isCyclic_of_card_le_one A hs
    exact hnc (isCyclic_of_surjective e.symm e.symm.surjective)
  have hprod : (∏ i,n i)=Nat.card G := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_pi]
    simp only [Fintype.card_multiplicative,ZMod.card]
  have hsum : (∑ i,n i)≤6 := cyclicProduct_sum_le_six_of_order_eight_or_nine
    n (fun i => hn i) hI (by simpa only [hprod] using hG)
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hpos : 0<∑ i,n i := Finset.sum_pos (fun i _ => by have hi:=hn i;omega)
    Finset.univ_nonempty
  let points : (Σ i,A i)≃Fin (∑ i,n i) := Fintype.equivFinOfCardEq (by
    rw [Fintype.card_sigma]
    simp only [A,Fintype.card_multiplicative,ZMod.card])
  let f : G→*Equiv.Perm (Fin (∑ i,n i)) := points.permCongrHom.toMonoidHom.comp
    ((productDisjointRegularAction A).comp e.toMonoidHom)
  exact ⟨∑ i,n i,hpos,hsum,f,points.permCongrHom.injective.comp
    ((productDisjointRegularAction_injective A).comp e.injective)⟩

end SymmetricSubgroupAsymptotics
