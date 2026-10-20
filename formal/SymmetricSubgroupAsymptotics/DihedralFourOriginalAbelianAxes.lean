import SymmetricSubgroupAsymptotics.TwoAxisAbelianizationCover
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Short original derived-word identities give the same two abelian
axes for rows108/109/154/155. The last action may retain a cyclic-four
axis; no exponent-two replacement of its original abelianization is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.DihedralFourOriginalAbelianAxes
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def generators : Fin 4 → Fin 4 → Equiv.Perm (Fin 12) :=
  ![row108Generators,row109Generators,row154Generators,row155Generators]
abbrev U (r : Fin 4) := Subgroup.closure (Set.range (generators r))
def original (r : Fin 4) : Fin 4 → U r := closureGenerators (generators r)
abbrev a (r : Fin 4) : U r := original r 2
abbrev b (r : Fin 4) : U r := original r 3
private def commTwo (i : Fin 4) : DerivedGeneratorWord (Fin 4) :=
  .mul (.conj 2 (.comm 2 i)) (.comm 2 i)
private def commFour (i : Fin 4) : DerivedGeneratorWord (Fin 4) :=
  .mul (.conj 2 (.conj 2 (commTwo i))) (commTwo i)
private def activeWord (i : Fin 4) : DerivedGeneratorWord (Fin 4) :=
  .mul (commTwo i) (commFour i)
private def firstWord (r : Fin 4) : DerivedGeneratorWord (Fin 4) :=
  if r.val<2 then activeWord 0 else .comm 2 3
private def secondWord (r : Fin 4) : DerivedGeneratorWord (Fin 4) :=
  if r.val<2 then activeWord 1 else .comm 2 1
private def correction (r : Fin 4) : U r := if r=3 then b r^2 else 1

private theorem first_identity (r : Fin 4) :
    original r 0=(firstWord r).eval (original r)*correction r := by
  fin_cases r <;> apply Subtype.ext <;> decide +kernel
private theorem second_identity (r : Fin 4) :
    original r 1=(secondWord r).eval (original r) := by
  fin_cases r <;> apply Subtype.ext <;> decide +kernel

private theorem derived_killed (r : Fin 4) (w : DerivedGeneratorWord (Fin 4)) :
    TwoAxisAbelianizationCover.q (w.eval (original r))=1 :=
  (QuotientGroup.eq_one_iff _).mpr (w.eval_mem_commutator (original r))

theorem generator_axes (r : Fin 4) (i : Fin 4) :
    TwoAxisAbelianizationCover.q (original r i) ∈
      TwoAxisAbelianizationCover.Left (a r) ⊔ TwoAxisAbelianizationCover.Right (b r) := by
  let q : U r →* U r ⧸ commutator (U r) := TwoAxisAbelianizationCover.q
  have hc : q (correction r)∈TwoAxisAbelianizationCover.Right (b r) := by
    by_cases hr : r=3
    · change q (if r=3 then b r^2 else 1)∈_
      rw [if_pos hr,q.map_pow]
      exact (TwoAxisAbelianizationCover.Right (b r)).pow_mem (Subgroup.mem_zpowers (q (b r))) 2
    · change q (if r=3 then b r^2 else 1)∈_
      rw [if_neg hr,q.map_one]
      exact Subgroup.one_mem _
  have h0 : q (original r 0)=q (correction r) := by
    calc
      q (original r 0)=q ((firstWord r).eval (original r)*correction r) :=
        congrArg q (first_identity r)
      _ = q (correction r) := by rw [q.map_mul,derived_killed,one_mul]
  have h1 : q (original r 1)=1 :=
    (congrArg q (second_identity r)).trans (derived_killed r (secondWord r))
  fin_cases i
  · change q (original r 0)∈_
    rw [h0]
    exact Subgroup.mem_sup_right hc
  · change q (original r 1)∈_
    rw [h1]
    exact Subgroup.one_mem _
  · change q (a r)∈_
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers (q (a r)))
  · change q (b r)∈_
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (q (b r)))

def cover (r : Fin 4) := TwoAxisAbelianizationCover.cover (a r) (b r)
theorem cover_surjective (r : Fin 4) : Function.Surjective (cover r) :=
  TwoAxisAbelianizationCover.cover_surjective (a r) (b r) (original r)
    (closureGenerators_full (generators r)) (generator_axes r)

end SymmetricSubgroupAsymptotics.DihedralFourOriginalAbelianAxes
