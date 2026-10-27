import SymmetricSubgroupAsymptotics.CFSGJankoTwoActualHeisenbergFrame
import SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
import SymmetricSubgroupAsymptotics.External.CFSG.Models.Presentations.J2

/-! Same-factor degree transport for the ORIGINAL J2 presentation, using
the genuine Heisenberg/Singer frame constructed from its literal matrix
representation. No ambient order, outer group or named-model assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleJankoTwoHeisenbergSingerExclusion
open PrimitiveSocleRawStructure

theorem degree_ge_twentySeven
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    27 ≤ Nat.card X := by
  letI : Finite CFSG.Models.Presentations.J2.Model := Finite.of_equiv D.Simple e.toEquiv
  letI : IsSimpleGroup CFSG.Models.Presentations.J2.Model := e.symm.isSimpleGroup
  exact SimpleModelMinimumIndexDegreeTransport.degree_ge D e 27
    (fun H hH => TernaryHeisenbergSingerGeneratorFrame.proper_index_ge_twentySeven
      CFSGJankoTwoActualHeisenbergFrame.frame H hH)

theorem not_jankoTwo_of_degree_le_twentyOne
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 21)
    (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    False := by
  have h27 := degree_ge_twentySeven D e
  omega

theorem not_jankoTwo_of_degree_le_ten
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X) (hsmall : Nat.card X ≤ 10)
    (e : D.Simple ≃* CFSG.Models.Presentations.J2.Model) :
    False := by
  exact not_jankoTwo_of_degree_le_twentyOne D (by omega) e

end SymmetricSubgroupAsymptotics.PrimitiveSocleJankoTwoHeisenbergSingerExclusion
