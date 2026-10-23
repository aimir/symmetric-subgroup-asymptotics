import SymmetricSubgroupAsymptotics.AbelianExtensionConjugation
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! EVERY actual joint quotient fibre of commuting pairs in an abelian
extension injects into the corresponding fibre of its associated split
extension. A commuting original base pair supplies the coordinates when
the fibre is nonempty. Empty fibres contribute zero. No section of the
extension, independent fibre product, or supplied comparison is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AbelianExtensionCommutingFibres
open AbelianExtensionConjugation

abbrev CommutingPairs (H:Type*) [Group H] := {p:H×H // Commute p.1 p.2}

def pairImage {H Q:Type*} [Group H] [Group Q] (f:H→*Q) (z:CommutingPairs H) : Q×Q :=
  (f z.val.1,f z.val.2)

abbrev Fibre {H Q:Type*} [Group H] [Group Q] (f:H→*Q) (p:Q×Q) :=
  {z:CommutingPairs H // pairImage f z=p}

variable {G:Type*} [Group G] (N:Subgroup G) [N.Normal]

def relativePart (x y:G) (h:QuotientGroup.mk' N x=QuotientGroup.mk' N y) : N :=
  ⟨x*y⁻¹,by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (x*y⁻¹)=1
    rw [map_mul,map_inv,h,mul_inv_cancel]⟩

def coefficients (p:(G⧸N)×(G⧸N)) (b z:Fibre (QuotientGroup.mk' N) p) : N×N :=
  (relativePart N z.val.val.1 b.val.val.1
      ((congrArg Prod.fst z.property).trans (congrArg Prod.fst b.property).symm),
    relativePart N z.val.val.2 b.val.val.2
      ((congrArg Prod.snd z.property).trans (congrArg Prod.snd b.property).symm))

theorem coefficients_reconstruct_fst (p:(G⧸N)×(G⧸N))
    (b z:Fibre (QuotientGroup.mk' N) p) :
    ((coefficients N p b z).1:G)*b.val.val.1=z.val.val.1 := by
  change (z.val.val.1*b.val.val.1⁻¹)*b.val.val.1=z.val.val.1
  group

theorem coefficients_reconstruct_snd (p:(G⧸N)×(G⧸N))
    (b z:Fibre (QuotientGroup.mk' N) p) :
    ((coefficients N p b z).2:G)*b.val.val.2=z.val.val.2 := by
  change (z.val.val.2*b.val.val.2⁻¹)*b.val.val.2=z.val.val.2
  group

theorem coefficients_injective (p:(G⧸N)×(G⧸N)) (b:Fibre (QuotientGroup.mk' N) p) :
    Function.Injective (coefficients N p b) := by
  intro z w he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have h := congrArg (fun c:N×N=>(c.1:G)*b.val.val.1) he
    exact (coefficients_reconstruct_fst N p b z).symm.trans
      (h.trans (coefficients_reconstruct_fst N p b w))
  · have h := congrArg (fun c:N×N=>(c.2:G)*b.val.val.2) he
    exact (coefficients_reconstruct_snd N p b z).symm.trans
      (h.trans (coefficients_reconstruct_snd N p b w))

theorem coefficients_commute_eq (p:(G⧸N)×(G⧸N)) (b z:Fibre (QuotientGroup.mk' N) p) :
    (coefficients N p b z).1*MulAut.conjNormal b.val.val.1 (coefficients N p b z).2=
      (coefficients N p b z).2*MulAut.conjNormal b.val.val.2 (coefficients N p b z).1 := by
  apply (commute_translates_iff N b.val.val.1 b.val.val.2 b.val.property
    (coefficients N p b z).1 (coefficients N p b z).2).mp
  rw [coefficients_reconstruct_fst,coefficients_reconstruct_snd]
  exact z.val.property

variable [IsMulCommutative N]

def splitPair (p:(G⧸N)×(G⧸N)) (b z:Fibre (QuotientGroup.mk' N) p) :
    CommutingPairs (AssociatedSplit N) :=
  ⟨(⟨(coefficients N p b z).1,p.1⟩,⟨(coefficients N p b z).2,p.2⟩),by
    change (⟨(coefficients N p b z).1,p.1⟩:AssociatedSplit N)*
        ⟨(coefficients N p b z).2,p.2⟩=
      ⟨(coefficients N p b z).2,p.2⟩*⟨(coefficients N p b z).1,p.1⟩
    apply SemidirectProduct.ext
    · change (coefficients N p b z).1*quotientConjugation N p.1 (coefficients N p b z).2=
        (coefficients N p b z).2*quotientConjugation N p.2 (coefficients N p b z).1
      have hb₁ : QuotientGroup.mk' N b.val.val.1=p.1 := congrArg Prod.fst b.property
      have hb₂ : QuotientGroup.mk' N b.val.val.2=p.2 := congrArg Prod.snd b.property
      rw [←hb₁,←hb₂,quotientConjugation_mk,quotientConjugation_mk]
      exact coefficients_commute_eq N p b z
    · change p.1*p.2=p.2*p.1
      have he : QuotientGroup.mk' N b.val.val.1*QuotientGroup.mk' N b.val.val.2=
          QuotientGroup.mk' N b.val.val.2*QuotientGroup.mk' N b.val.val.1 := by
        simpa only [map_mul] using congrArg (QuotientGroup.mk' N) b.val.property
      have hb₁ : QuotientGroup.mk' N b.val.val.1=p.1 := congrArg Prod.fst b.property
      have hb₂ : QuotientGroup.mk' N b.val.val.2=p.2 := congrArg Prod.snd b.property
      simpa only [hb₁,hb₂] using he⟩

def splitFibreMap (p:(G⧸N)×(G⧸N)) (b:Fibre (QuotientGroup.mk' N) p) :
    Fibre (QuotientGroup.mk' N) p→Fibre
      (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p :=
  fun z=>⟨splitPair N p b z,rfl⟩

theorem splitFibreMap_injective (p:(G⧸N)×(G⧸N)) (b:Fibre (QuotientGroup.mk' N) p) :
    Function.Injective (splitFibreMap N p b) := by
  intro z w he
  apply coefficients_injective N p b
  apply Prod.ext
  · exact congrArg (fun u:Fibre (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p=>
      u.val.val.1.left) he
  · exact congrArg (fun u:Fibre (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p=>
      u.val.val.2.left) he

theorem commuting_fibre_card_le [Finite G] (p:(G⧸N)×(G⧸N)) :
    Nat.card (Fibre (QuotientGroup.mk' N) p)≤Nat.card
      (Fibre (SemidirectProduct.rightHom:AssociatedSplit N→*(G⧸N)) p) := by
  by_cases hb : Nonempty (Fibre (QuotientGroup.mk' N) p)
  · let b := Classical.choice hb
    exact Nat.card_le_card_of_injective (splitFibreMap N p b) (splitFibreMap_injective N p b)
  · letI : IsEmpty (Fibre (QuotientGroup.mk' N) p) := not_nonempty_iff.mp hb
    have hz : Nat.card (Fibre (QuotientGroup.mk' N) p)=0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz]
    exact Nat.zero_le _

end SymmetricSubgroupAsymptotics.AbelianExtensionCommutingFibres
