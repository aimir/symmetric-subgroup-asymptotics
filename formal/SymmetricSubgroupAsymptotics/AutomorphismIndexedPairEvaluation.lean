import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSylowOuterNormalization

/-! Dependent accepted-image incidence: each actual first image retains
its own accepted second-image set. No finite capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AutomorphismIndexedPairEvaluation

variable {G : Type} [Group G] [Finite G]

def evaluation {I : Type} (S : Subgroup (MulAut G)) (_u v : G)
    (_first : I → G) (label : S → I)
    (accepted : I → Finset G)
    (haccepted : ∀ f : S, f.val v ∈ accepted (label f)) :
    S → (i : I) × accepted i := fun f => ⟨label f,⟨f.val v,haccepted f⟩⟩

omit [Finite G] in
theorem evaluation_injective {I : Type} (S : Subgroup (MulAut G)) (u v : G)
    (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (first : I → G) (label : S → I)
    (hfirst : ∀ f : S, first (label f) = f.val u)
    (accepted : I → Finset G)
    (haccepted : ∀ f : S, f.val v ∈ accepted (label f)) :
    Function.Injective (evaluation S u v first label accepted haccepted) := by
  intro f h he
  apply Subtype.ext
  apply MulEquiv.ext
  intro z
  have hu : f.val u = h.val u := by
    rw [←hfirst f,←hfirst h]
    exact congrArg (fun p : (i : I) × accepted i => first p.1) he
  have hv : f.val v = h.val v :=
    congrArg (fun p : (i : I) × accepted i => p.2.val) he
  have hm : f.val.toMonoidHom = h.val.toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    rintro w (rfl|rfl)
    · exact hu
    · exact hv
  exact DFunLike.congr_fun hm z

theorem card_le_sum_accepted {I : Type} [Fintype I]
    (S : Subgroup (MulAut G)) (u v : G)
    (hgen : Subgroup.closure ({u,v} : Set G) = ⊤)
    (first : I → G) (label : S → I)
    (hfirst : ∀ f : S, first (label f) = f.val u)
    (accepted : I → Finset G)
    (haccepted : ∀ f : S, f.val v ∈ accepted (label f)) :
    Nat.card S ≤ ∑ i : I, (accepted i).card := by
  have hh := Nat.card_le_card_of_injective (evaluation S u v first label accepted haccepted)
    (evaluation_injective S u v hgen first label hfirst accepted haccepted)
  simpa only [Nat.card_sigma,Nat.card_eq_fintype_card,Fintype.card_sigma,Fintype.card_coe] using hh

end SymmetricSubgroupAsymptotics.AutomorphismIndexedPairEvaluation

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoIndexedOuterIncidence
open PrimitiveSocleRawStructure CFSGMathieuTwentyTwoElevenGeneration
open CFSGMathieuTwentyTwoSylowOuterNormalization

private instance modelFinite : Finite CFSG.Models.Mathieu22 := Finite.of_injective
  (fun g : CFSG.Models.Mathieu22 => g.val) Subtype.val_injective
private instance modelFintype : Fintype CFSG.Models.Mathieu22 := Fintype.ofFinite _
private instance powersFintype : Fintype nontrivialFirstPowers :=
  Fintype.ofFinite {z : selectedSylow // z.val ≠ (1 : CFSG.Models.Mathieu22)}

def firstImage (f : preservingAutomorphisms) : nontrivialFirstPowers :=
  (CFSGMathieuTwentyTwoSylowOuterNormalization.evaluation Finset.univ (by simp) f).1

theorem outer_mul_fiftyFive_le_sum_accepted
    [IsSimpleGroup CFSG.Models.Mathieu22]
    (accepted : nontrivialFirstPowers → Finset CFSG.Models.Mathieu22)
    (haccepted : ∀ f : preservingAutomorphisms, f.val secondElement ∈ accepted (firstImage f)) :
    Nat.card (Outer CFSG.Models.Mathieu22) * 55 ≤
      ∑ p : nontrivialFirstPowers, (accepted p).card := by
  rw [outer_mul_fiftyFive_eq_preservingAutomorphisms]
  exact AutomorphismIndexedPairEvaluation.card_le_sum_accepted
    preservingAutomorphisms firstElement secondElement closure_pair_eq_top
    (fun p : nontrivialFirstPowers => p.val.val) firstImage (fun _ => rfl)
    accepted haccepted

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoIndexedOuterIncidence
