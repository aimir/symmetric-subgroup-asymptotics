import SymmetricSubgroupAsymptotics.CFSGMathieuElevenActualClassCount
import Mathlib.GroupTheory.GroupAction.Basic

/-! The certified ten-class cover has a unique order-four row. Thus every
order-four element of the SAME original permutation subgroup is conjugate
inside that subgroup to its original generator b. The certified FourA
centralizer cardinal transfers along actual conjugacy, without simplicity
or an automorphism-order assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenOrderFourConjugacy
open CFSG.Certificates.Mathieu11
open M11Certificates.ConjugacyClasses
open CFSGMathieuElevenPresentationWords

private theorem order_four_row (g : M11) (hg : orderOf g = 4) :
    IsConj g (representativeM11 rep4AIndex) := by
  obtain ⟨i,hi⟩ := CFSGMathieuElevenActualClassCount.original_representative_cover g
  have ho : classElementOrder i = 4 :=
    (representativeM11_orderOf_eq i).symm.trans ((orderOf_eq_of_isConj hi).symm.trans hg)
  have hrow : ∀ j : Fin 10, classElementOrder j = 4 → j = rep4AIndex := by
    decide +kernel
  exact hrow i ho ▸ hi

private theorem originalB_order : orderOf originalB = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq : originalB ^ 2 ≠ 1 := by
    have hmove : (m11b ^ 2) (2 : Fin 11) ≠ 2 := by decide +kernel
    intro h
    have he : M11Subgroup.subtype (originalB ^ 2) = M11Subgroup.subtype 1 :=
      congrArg M11Subgroup.subtype h
    rw [map_pow,map_one] at he
    have hb : M11Subgroup.subtype originalB = m11b := rfl
    rw [hb] at he
    exact hmove (congrArg (fun u : Perm11 => u (2 : Fin 11)) he)
  have hfour : originalB ^ 4 = 1 := by
    change y ^ 4 = 1
    exact relator_one
  exact orderOf_eq_prime_pow (x := originalB) (p := 2) (n := 1) hsq hfour

theorem isConj_originalB_of_order_four (g : M11) (hg : orderOf g = 4) :
    IsConj g originalB :=
  (order_four_row g hg).trans (order_four_row originalB originalB_order).symm

theorem originalB_centralizer_card :
    Nat.card (Subgroup.centralizer ({originalB} : Set M11)) = 8 := by
  classical
  have hc := order_four_row originalB originalB_order
  have hrel : MulAction.orbitRel (ConjAct M11) M11 originalB
      (representativeM11 rep4AIndex) := by
    rw [ConjAct.orbitRel_conjAct]
    exact hc
  calc
    _ = Fintype.card (MulAction.stabilizer (ConjAct M11) originalB) :=
      (conjActStabilizer_card_eq_centralizer_card originalB).symm
    _ = Fintype.card (MulAction.stabilizer (ConjAct M11)
        (representativeM11 rep4AIndex)) :=
      Fintype.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hrel).toEquiv
    _ = Nat.card (RepresentativeCentralizer rep4AIndex) :=
      conjActStabilizer_card_eq_centralizer_card (representativeM11 rep4AIndex)
    _ = 8 := rep4A_centralizer_card

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenOrderFourConjugacy
