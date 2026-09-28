import SymmetricSubgroupAsymptotics.FusionPhysicalCount

/-!
# Source-restricted physical fusion families

Some sharp local envelopes apply only after an earlier consumer has left a
specified property on the complete undeleted source.  This file makes that
property part of the physical fusion predicate.  On a literal Goursat
reconstruction the second projection is exactly the same source subgroup
`J`, so no marking hypothesis has to be supplied again at the numerical
consumer.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {Ω Z : Type*}

/-- Retain both an arbitrary physical predicate and a property of the whole
undeleted complement image. -/
def FusionSourceRestrictedPredicate
    (U : Subgroup (Equiv.Perm Ω))
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (Source : Subgroup (Equiv.Perm Z) → Prop)
    (H : Subgroup (U × Equiv.Perm Z)) : Prop :=
  P H ∧ Source (H.map (MonoidHom.snd U (Equiv.Perm Z)))

/-- Conjugacy invariance of the retained source property gives exactly the
normalizer naturality required by original-weight physical counting. -/
theorem fusionSourceRestrictedPredicate_natural
    (U : Subgroup (Equiv.Perm Ω))
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (Source : Subgroup (Equiv.Perm Z) → Prop)
    (hP : FusionOrbitNatural U P)
    (hSource : ∀ c : Equiv.Perm Z, ∀ J,
      Source J → Source (J.map (MulAut.conj c).toMonoidHom)) :
    FusionOrbitNatural U
      (FusionSourceRestrictedPredicate U P Source) := by
  exact fusionOrbitNatural_and U P
    (fun H => Source (H.map (MonoidHom.snd U (Equiv.Perm Z)))) hP
    (fusionOrbitNatural_source U Source hSource)

/-- The source mark is literal on every full Goursat reconstruction: its
second projection is `J`, not an enlargement or an independently chosen
copy. -/
theorem fusionSourceRestrictedPredicate_encode_source
    (U : Subgroup (Equiv.Perm Ω))
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (Source : Subgroup (Equiv.Perm Z) → Prop)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm Z))
    (β : GroupEpimorphism J (U ⧸ N.1))
    (h : FusionSourceRestrictedPredicate U P Source
      (fusionFullGoursatEncode N J β).1) :
    Source J := by
  have hsource := h.2
  change Source
    ((fusionQuotientGraph (QuotientGroup.mk' N.1) J β.1).map
      (MonoidHom.snd U (Equiv.Perm Z))) at hsource
  rwa [fusionQuotientGraph_complement
    (QuotientGroup.mk' N.1) (QuotientGroup.mk'_surjective N.1)] at hsource

end SymmetricSubgroupAsymptotics

end
