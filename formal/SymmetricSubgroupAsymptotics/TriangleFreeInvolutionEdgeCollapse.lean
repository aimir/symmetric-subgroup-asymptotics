import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Logic.Relation

/-! A shared noncollapse lemma for connected triangle-free involution
presentations. Adjacent products have cube one; distinct nonadjacent
products have square one. If one adjacent pair of generators coincides,
EVERY generator coincides, and the actual generated group is cyclic.
The conclusion applies after ANY surjective homomorphism. It does NOT
assert that a parabolic embeds or identify a finite Coxeter group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TriangleFreeInvolutionEdgeCollapse

variable {G : Type*} [Group G] {ι : Type*} (g : ι → G) (R : ι → ι → Prop)
    (hsq : ∀ i, g i ^ 2 = 1)
    (htriangle : ∀ i j k, R i j → R j k → ¬ R i k)
    (hedge : ∀ i j, R i j → (g i*g j)^3 = 1)
    (haway : ∀ i j, i ≠ j → ¬ R i j → (g i*g j)^2 = 1)

include hsq htriangle hedge haway

private theorem neighbor_equal_of_collapsed_edge
    (u v : ι) (huv : R u v) (heq : g u = g v) (w : ι) (hvw : R v w) :
    g w = g v := by
  by_cases hwu : w = u
  · subst w
    exact heq
  have h2 : (g u*g w)^2 = 1 := haway u w (Ne.symm hwu) (htriangle u v w huv hvw)
  have h3 : (g u*g w)^3 = 1 := by
    rw [heq]
    exact hedge v w hvw
  have hp : g u*g w = 1 := by
    have hh : (g u*g w)^2*(g u*g w) = 1 := by simpa only [pow_succ] using h3
    rwa [h2,one_mul] at hh
  have huu : g u*g u = 1 := by simpa only [pow_two] using hsq u
  have hwu' : g w = g u := by
    calc
      g w = (g u*g u)*g w := by rw [huu,one_mul]
      _ = g u*(g u*g w) := mul_assoc _ _ _
      _ = g u := by rw [hp,mul_one]
  exact hwu'.trans heq

/-- The connected presentation is cyclic as soon as ONE edge collapses.
No finiteness, faithful representation or catalogue premise is used. -/
theorem isCyclic_of_adjacent_eq
    (hsymm : ∀ i j, R i j → R j i)
    (hconn : ∀ i j, Relation.ReflTransGen R i j)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (i j : ι) (hij : R i j) (heq : g i = g j) : IsCyclic G := by
  have hstate : ∀ {a : ι}, Relation.ReflTransGen R i a →
      g a = g i ∧ ∀ b, R a b → g b = g i := by
    intro a h
    induction h with
    | refl =>
      refine ⟨rfl,?_⟩
      intro b hib
      exact neighbor_equal_of_collapsed_edge g R hsq htriangle hedge haway
        j i (hsymm i j hij) heq.symm b hib
    | tail _ hlast ih =>
      have hnext := ih.2 _ hlast
      refine ⟨hnext,?_⟩
      intro b hnb
      exact (neighbor_equal_of_collapsed_edge g R hsq htriangle hedge haway
        _ _ hlast (ih.1.trans hnext.symm) b hnb).trans hnext
  have hall (a : ι) : g a = g i := (hstate (hconn i a)).1
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨g i,le_antisymm le_top ?_⟩
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a,rfl⟩
  rw [hall a]
  exact Subgroup.mem_zpowers _

/-- A noncommutative quotient keeps EVERY adjacent pair distinct. This
is only noncollapse; injectivity of a proposed parabolic is a further
structural theorem and is not assumed or inferred here. -/
theorem adjacent_images_ne_of_noncommutative_quotient
    (hsymm : ∀ i j, R i j → R j i)
    (hconn : ∀ i j, Relation.ReflTransGen R i j)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    {H : Type*} [Group H] (f : G →* H) (hf : Function.Surjective f)
    (hn : ¬ IsMulCommutative H) (i j : ι) (hij : R i j) : f (g i) ≠ f (g j) := by
  intro heq
  have hgenH : Subgroup.closure (Set.range (f ∘ g)) = ⊤ := by
    rw [Set.range_comp,← MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective f hf
  have hsqH (a : ι) : (f (g a))^2 = 1 := by rw [← map_pow,hsq,map_one]
  have hedgeH (a b : ι) (hab : R a b) : (f (g a)*f (g b))^3 = 1 := by
    rw [← map_mul,← map_pow,hedge a b hab,map_one]
  have hawayH (a b : ι) (hab : a ≠ b) (hR : ¬ R a b) :
      (f (g a)*f (g b))^2 = 1 := by
    rw [← map_mul,← map_pow,haway a b hab hR,map_one]
  letI : IsCyclic H := isCyclic_of_adjacent_eq (f ∘ g) R hsqH htriangle hedgeH hawayH
    hsymm hconn hgenH i j hij heq
  exact hn inferInstance

end SymmetricSubgroupAsymptotics.TriangleFreeInvolutionEdgeCollapse
