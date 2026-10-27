import SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound

/-! Count automorphisms fixing one generator from an indexed cover of the
other generator's actual images. The target is a dependent sum, so overlaps
between the accepted image sets only increase the resulting upper bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteIndexedAutomorphismImageCapacity

open OuterFixedElementEvaluationBound

theorem fixedAutomorphisms_card_le_sum
    {G : Type} [Group G] [Finite G] {I : Type} [Fintype I]
    (u v : G) (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (accepted : I → Finset G)
    (hcover : ∀ f : fixedAutomorphisms v, ∃ i : I, f.val u ∈ accepted i) :
    Nat.card (fixedAutomorphisms v) ≤ ∑ i : I, (accepted i).card := by
  let label : fixedAutomorphisms v → I := fun f => Classical.choose (hcover f)
  have haccepted : ∀ f : fixedAutomorphisms v, f.val u ∈ accepted (label f) :=
    fun f => Classical.choose_spec (hcover f)
  let eval : fixedAutomorphisms v → (i : I) × accepted i :=
    fun f => ⟨label f,⟨f.val u,haccepted f⟩⟩
  have hinj : Function.Injective eval := by
    intro f h he
    apply Subtype.ext
    apply MulEquiv.ext
    intro z
    have hu : f.val u = h.val u :=
      congrArg (fun p : (i : I) × accepted i => p.2.val) he
    have hm : f.val.toMonoidHom = h.val.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      rintro w (rfl|rfl)
      · exact hu
      · exact f.property.trans h.property.symm
    exact DFunLike.congr_fun hm z
  have hc := Nat.card_le_card_of_injective eval hinj
  simpa only [Nat.card_sigma,Nat.card_eq_fintype_card,
    Fintype.card_sigma,Fintype.card_coe] using hc

end SymmetricSubgroupAsymptotics.FiniteIndexedAutomorphismImageCapacity
