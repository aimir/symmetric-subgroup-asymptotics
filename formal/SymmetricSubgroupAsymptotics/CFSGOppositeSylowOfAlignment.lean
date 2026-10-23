import SymmetricSubgroupAsymptotics.CFSGOppositeSylowPairAlignment
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint

/-! One known disjoint Sylow pair and actual positive-conjugator
alignment identify its prescribed negative target as a Sylow. This
avoids assuming in advance that an ambient fixed negative group lies
in a chosen original preimage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment
open CFSGSubgroupConjugateDisjoint
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_negative_sylow (P Q : Sylow p G) (V : Subgroup G)
    (hPQ : (P : Subgroup G)⊓(Q : Subgroup G)=⊥)
    (halign : ∀g : G,(P : Subgroup G)⊓
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom=⊥→
        ∃b∈(P : Subgroup G),(P : Subgroup G).map (MulAut.conj g).toMonoidHom=
          V.map (MulAut.conj b).toMonoidHom) :
    ∃S : Sylow p G,(S : Subgroup G)=V ∧ (P : Subgroup G)⊓(S : Subgroup G)=⊥ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have hgmap : (P : Subgroup G).map (MulAut.conj g).toMonoidHom=(Q : Subgroup G) :=
    congrArg (fun R : Sylow p G=>(R : Subgroup G)) hg
  obtain ⟨b,hb,he⟩ := halign g (by rw [hgmap];exact hPQ)
  have hQV : (Q : Subgroup G)=V.map (MulAut.conj b).toMonoidHom := hgmap.symm.trans he
  have hcard := Nat.card_congr ((MulAut.conj b).subgroupMap V).toEquiv
  change Nat.card V=Nat.card (V.map (MulAut.conj b).toMonoidHom) at hcard
  rw [←hQV] at hcard
  have horder : Nat.card V=p^(Nat.card G).factorization p :=
    hcard.trans Q.card_eq_multiplicity
  let S := Sylow.ofCard V horder
  have hS : (S : Subgroup G)=V := Sylow.coe_ofCard V horder
  refine ⟨S,hS,?_⟩
  rw [hS]
  apply (inf_conjugate_eq_bot_iff (P : Subgroup G) V b ((P : Subgroup G).le_normalizer hb)).mp
  rw [←hQV]
  exact hPQ

theorem exists_inner_fix_pair (P Q : Sylow p G) (V : Subgroup G)
    (hPQ : (P : Subgroup G)⊓(Q : Subgroup G)=⊥)
    (halign : ∀g : G,(P : Subgroup G)⊓
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom=⊥→
        ∃b∈(P : Subgroup G),(P : Subgroup G).map (MulAut.conj g).toMonoidHom=
          V.map (MulAut.conj b).toMonoidHom)
    (f : MulAut G) :
    ∃g : G,(P : Subgroup G).map (MulAut.conj g*f).toMonoidHom=(P : Subgroup G) ∧
      V.map (MulAut.conj g*f).toMonoidHom=V := by
  obtain ⟨S,hS,hPS⟩ := exists_negative_sylow P Q V hPQ halign
  obtain ⟨g,hgP,hgS⟩ := CFSGOppositeSylowPairAlignment.exists_inner_fix_pair P S hPS (fun a ha=>by
    obtain ⟨b,hb,he⟩ := halign a ha
    refine ⟨b,(P : Subgroup G).le_normalizer hb,?_⟩
    simpa only [hS] using he) f
  refine ⟨g,?_,?_⟩
  · exact congrArg (fun R : Sylow p G=>(R : Subgroup G)) hgP
  · have hh := congrArg (fun R : Sylow p G=>(R : Subgroup G)) hgS
    change (S : Subgroup G).map (MulAut.conj g*f).toMonoidHom=(S : Subgroup G) at hh
    simpa only [hS] using hh

end SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment
