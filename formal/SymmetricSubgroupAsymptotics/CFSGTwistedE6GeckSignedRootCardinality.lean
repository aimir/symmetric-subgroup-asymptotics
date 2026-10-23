import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalSignedRootAction

/-! Intrinsically recovered original root charts retain their actual
sizes q^2 on paired labels and q on singleton labels. Thus the proved
signed root permutation preserves the two literal label classes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootCardinality
open CFSGTwistedE6GeckOriginalSignedRootAction CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalNegativeRootAction CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGE6GeckFixedOrbitRootGroups

theorem originalSignedRoot_paired (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    originalSignedRoot q neg (pairedOrbit j)=(pairedOriginalHom q neg j).range := by
  cases neg
  · exact originalOrbitRoot_paired q j
  · exact originalNegativeOrbitRoot_paired q j

theorem originalSignedRoot_singleton (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (j : Fin 2) :
    originalSignedRoot q neg (singletonOrbit j)=(singletonOriginalHom q neg j).range := by
  cases neg
  · exact originalOrbitRoot_singleton q j
  · exact originalNegativeOrbitRoot_singleton q j

theorem originalSignedRoot_card (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (neg : Bool) (a : Fin 4) :
    Nat.card (originalSignedRoot q neg a)=if a.val<2 then q.order^2 else q.order := by
  have hp (j : Fin 2) : Nat.card (originalSignedRoot q neg (pairedOrbit j))=q.order^2 := by
    rw [originalSignedRoot_paired,pairedOriginalHom_range_card]
  have hs (j : Fin 2) : Nat.card (originalSignedRoot q neg (singletonOrbit j))=q.order := by
    rw [originalSignedRoot_singleton,singletonOriginalHom_range_card]
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

theorem root_permutation_preserves_shape (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (f : MulAut (CFSG.Models.TwistedE6 q))
    (sigma : Equiv.Perm (Fin 4))
    (hsigma : ∀a,(originalSignedRoot q false a).map f.toMonoidHom=
      originalSignedRoot q false (sigma a)) (a : Fin 4) :
    (sigma a).val<2 ↔ a.val<2 := by
  have hc := congrArg (fun S : Subgroup (CFSG.Models.TwistedE6 q)=>Nat.card S) (hsigma a)
  dsimp only at hc
  rw [Subgroup.card_map_of_injective f.injective,originalSignedRoot_card,originalSignedRoot_card] at hc
  have hq : 2≤q.order := by
    rw [←q.card_field]
    exact Finite.one_lt_card
  have hneq : q.order^2≠q.order := by nlinarith
  constructor
  · intro htarget
    by_contra hsource
    rw [if_neg hsource,if_pos htarget] at hc
    exact hneq hc.symm
  · intro hsource
    by_contra htarget
    rw [if_pos hsource,if_neg htarget] at hc
    exact hneq hc

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckSignedRootCardinality
