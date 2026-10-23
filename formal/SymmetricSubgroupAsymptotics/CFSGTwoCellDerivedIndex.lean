import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Finite.Sum
import Lean.Elab.Tactic.Omega

/-! A two-cell group whose root subgroup and torus squares are derived
has derived index at most four, provided the torus square subgroup has
index at most two. The quotient is explicitly covered by two copies of
the actual torus image. No perfectness assumption is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoCellDerivedIndex
variable {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]

theorem derived_index_le_four (B U : Subgroup G) (w : G) (f : A→*G)
    (hU : U≤commutator G) (hsquare : ∀a : A,f (a^2)∈commutator G)
    (hindex : (powMonoidHom 2:A→*A).range.index≤2)
    (hfactor : ∀b∈B,∃u∈U,∃a : A,b=u*f a)
    (hcover : ∀g : G,g∈B ∨ ∃b∈B,∃u∈U,g=b*w*u) :
    (commutator G).index≤4 := by
  let Q := G⧸commutator G
  let pi : G→*Q := QuotientGroup.mk' (commutator G)
  let torus : A→*Q := pi.comp f
  let R : Subgroup Q := torus.range
  letI : Finite R := Finite.of_surjective torus.rangeRestrict torus.rangeRestrict_surjective
  have hUone (u : G) (hu : u∈U) : pi u=1 :=
    (QuotientGroup.eq_one_iff u).mpr (hU hu)
  have hker : (powMonoidHom 2:A→*A).range≤torus.ker := by
    rintro _ ⟨a,rfl⟩
    change pi (f (a^2))=1
    exact (QuotientGroup.eq_one_iff _).mpr (hsquare a)
  have hRcard : Nat.card R≤2 := by
    change Nat.card torus.range≤2
    rw [←Subgroup.index_ker]
    exact (Subgroup.index_antitone hker).trans hindex
  have hBimage (b : G) (hb : b∈B) : pi b∈R := by
    obtain ⟨u,hu,a,rfl⟩ := hfactor b hb
    refine ⟨a,?_⟩
    change pi (f a)=pi (u*f a)
    rw [map_mul,hUone u hu,one_mul]
  let encode : R⊕R→Q := Sum.elim Subtype.val (fun r=>r.val*pi w)
  have hsurj : Function.Surjective encode := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) q
    rcases hcover g with hg|⟨b,hb,u,hu,he⟩
    · exact ⟨Sum.inl ⟨pi g,hBimage g hg⟩,rfl⟩
    · refine ⟨Sum.inr ⟨pi b,hBimage b hb⟩,?_⟩
      change pi b*pi w=pi g
      rw [he,map_mul,map_mul,hUone u hu,mul_one]
  have hc := Nat.card_le_card_of_surjective encode hsurj
  rw [Nat.card_sum] at hc
  rw [Subgroup.index_eq_card]
  change Nat.card Q≤4
  omega

end SymmetricSubgroupAsymptotics.CFSGTwoCellDerivedIndex
