import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! Every proper subgroup of the same pinned simple original ReeF4
model has index at least q. The actual fixed outer root group has order
q, and its nonidentity parameters are conjugate under the actual square
scalar action. The Tits parameter remains excluded by m>0. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPermutationDegree
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOuterTorusAction CFSGReeFFourFixedTorusGroup
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedAmbientHom
open CFSGConjugateSubgroupDegree PrimitiveSocleRawStructure MulAction

private theorem original_finite (m : ℕ) (hm : 0<m) : Finite (CFSG.Models.ReeF4 m) := by
  letI : Finite (originalModelFixed m) :=
    Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)
  exact Finite.of_surjective (fixedToOriginal m hm) (fixedToOriginal_surjective m hm)

theorem field_card_le_of_root_movement (m : ℕ) (hm : 0<m)
    {X : Type*} [Finite X] [MulAction (CFSG.Models.ReeF4 m) X]
    (hmove : ∃x : X,originalOuterHom m hm (Multiplicative.ofAdd 1) • x≠x) :
    Nat.card (Field m)≤Nat.card X := by
  letI : MulAction (Multiplicative (Field m)) X :=
    MulAction.compHom X (originalOuterHom m hm)
  rw [←show Nat.card (Multiplicative (Field m))=Nat.card (Field m) from
    Nat.card_congr Multiplicative.toAdd]
  apply card_le_of_constant_fixedBy
    (Nat.card (fixedBy X (originalOuterHom m hm (Multiplicative.ofAdd 1))))
  · intro a ha
    have ha0 : a.toAdd≠0 := by
      intro he
      exact ha (congrArg Multiplicative.ofAdd he)
    obtain ⟨t,ht⟩ := unit_square_surjective m (Units.mk0 a.toAdd ha0)
    have he := Nat.card_congr (fixedByConjugateEquiv (X:=X)
      (originalOuterHom m hm (Multiplicative.ofAdd 1)) (originalOuterTorus m hm t))
    rw [original_torus_outer_action] at he
    have htval : (1 : Field m)*(t : Field m)^2=a.toAdd := by
      have hv := congrArg (fun u : (Field m)ˣ=>(u : Field m)) ht
      simpa only [Units.val_pow_eq_pow_val,Units.val_mk0,one_mul] using hv
    rw [htval] at he
    simpa only [MulAction.fixedBy,MulAction.compHom_smul_def] using he.symm
  · obtain ⟨x,hx⟩ := hmove
    exact ⟨Multiplicative.ofAdd 1,x,hx⟩

theorem field_card_le_proper_index (m : ℕ) (hm : 0<m)
    [IsSimpleGroup (CFSG.Models.ReeF4 m)]
    (H : Subgroup (CFSG.Models.ReeF4 m)) (hH : H≠⊤) :
    Nat.card (Field m)≤H.index := by
  letI : Finite (CFSG.Models.ReeF4 m) := original_finite m hm
  change Nat.card (Field m)≤Nat.card (CFSG.Models.ReeF4 m ⧸ H)
  apply field_card_le_of_root_movement m hm
  apply exists_moved_coset_of_ne_one H hH
  intro he
  have hp := originalOuterHom_injective m hm
    (he.trans (map_one (originalOuterHom m hm)).symm)
  exact (show (1 : Field m)≠0 from one_ne_zero)
    (congrArg (fun z : Multiplicative (Field m)=>z.toAdd) hp)

theorem order_le_proper_index (m : ℕ) (hm : 0<m)
    [IsSimpleGroup (CFSG.Models.ReeF4 m)]
    (H : Subgroup (CFSG.Models.ReeF4 m)) (hH : H≠⊤) :
    2^(2*m+1)≤H.index := by
  simpa only [field_card] using field_card_le_proper_index m hm H hH

theorem order_le_leastProperIndex (m : ℕ) (hm : 0<m)
    [IsSimpleGroup (CFSG.Models.ReeF4 m)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeF4 m) ell) : 2^(2*m+1)≤ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact order_le_proper_index m hm H hH

end SymmetricSubgroupAsymptotics.CFSGReeFFourPermutationDegree
