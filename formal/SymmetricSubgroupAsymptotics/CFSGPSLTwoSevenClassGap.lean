import SymmetricSubgroupAsymptotics.CFSGPSLTwoOddTorusCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneOddClassCube
import SymmetricSubgroupAsymptotics.CFSGTypeARankTwoCardTwo
import SymmetricSubgroupAsymptotics.SmallFibreOrder168BinaryClassGap
import SymmetricSubgroupAsymptotics.SmallFibreNonaffinePerIndexClassResidual
import SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import Mathlib.Data.Nat.Prime.Int

/-! The original field-seven PSL2 model supplies its actual order168,
outer bound2 and class/outer product12. All actual small-fibre sources
are paid using the shared unsigned reserve on the binary seven/eight
seams and the existing all-factor recurrence elsewhere. No PSL3(2)
isomorphism, subgroup catalogue or new global input is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoSevenClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

theorem parameters (q : CFSG.PrimePower) (hq : q.order=7) :
    q.prime=7 ∧ q.exponent=1 :=
  Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 7)
    q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
    (show q.prime^q.exponent=7^1 from hq)

theorem order_eq_168 (q : CFSG.PrimePower) (hq : q.order=7) :
    Nat.card (CFSG.Models.A 1 q)=168 := by
  have hp := (parameters q hq).1
  have hchar : ringChar q.Field≠2 := by rw [ringChar.eq q.Field q.prime,hp]; decide
  have h := CFSGPSLTwoOddTorusCardinality.twice_projective_card_eq (F:=q.Field) hchar
  change 2*Nat.card (CFSG.Models.A 1 q)=
    (Nat.card q.Field-1)*Nat.card q.Field*(Nat.card q.Field+1) at h
  rw [q.card_field,hq] at h
  omega

theorem outer_card_le_two (q : CFSG.PrimePower) (hq : q.order=7) :
    Nat.card (Outer (CFSG.Models.A 1 q))≤2 := by
  have he := (parameters q hq).2
  have h := CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
  omega

theorem component_class_card_le_twelve (q : CFSG.PrimePower) (hq : q.order=7) :
    Nat.card (ConjClasses (CFSG.Models.A 1 q))*
      Nat.card (Outer (CFSG.Models.A 1 q))≤12 := by
  have hp := (parameters q hq).1
  have hc : Nat.card (ConjClasses (CFSG.Models.A 1 q))≤6 := by
    have h := CFSGTypeARankOneOddClassCube.twice_class_card_le q (by omega)
    omega
  exact (Nat.mul_le_mul hc (outer_card_le_two q hq)).trans_eq (by decide : 6*2=12)

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

/-- The actual original field-seven factor pays binary and ternary fibres,
all original factor counts and degree forms, and arbitrary subnormal H. -/
theorem subnormal_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=7)
    (e : E.Simple≃*CFSG.Models.A 1 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 1 q) := Finite.of_equiv E.Simple e.toEquiv
  have hclasses : Nat.card (ConjClasses E.Simple)=
      Nat.card (ConjClasses (CFSG.Models.A 1 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have hcardS : Nat.card E.Simple=168 :=
    (Nat.card_congr e.toEquiv).trans (order_eq_168 q hq)
  have houter : Nat.card (Outer E.Simple)≤2 := by
    rw [outer_card_congr e]
    exact outer_card_le_two q hq
  have hB : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤12 := by
    rw [hclasses,outer_card_congr e]
    exact component_class_card_le_twelve q hq
  have hindex : ∀K:Subgroup E.Simple,K≠⊤→7≤K.index := by
    intro K hK
    apply CFSGTypeARankTwoCardTwo.prime_le_proper_index 7 (by decide) ?_ K hK
    rw [hcardS]
    decide
  have hbudget : ∀K:Subgroup E.Simple,K≠⊤→
      (Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple))^3≤5^(K.index+1) := by
    intro K hK
    exact (Nat.pow_le_pow_left hB 3).trans
      ((by decide : (12:ℕ)^3≤5^8).trans
        (Nat.pow_le_pow_right (by decide) (by have h:=hindex K hK;omega)))
  have hsquare : ∀ell:ℕ,LeastProperIndex E.Simple ell→ell^2<Nat.card E.Simple := by
    intro ell hell
    rw [Nat.card_congr e.toEquiv]
    exact CFSGPSLTwoGeometry.leastProperIndex_square_lt_card (F:=q.Field)
      (by rw [q.card_field,hq];decide) ell (leastProperIndex_of_mulEquiv e ell hell)
  rcases SmallFibreNonaffinePerIndexClassResidual.subnormal_gap_or_least_short_index
      π hπ c hc hsize E hbudget hsquare H hH with
      hgap|⟨hk,ell,hell,K,hK,hdegree,hlo,hhi⟩
  · exact hgap
  · have hn : 7≤Nat.card X := by rw [hdegree];exact hindex K hK
    have hnine : Nat.card X≠9 := by
      intro he
      have hd : K.index∣168 := by simpa only [hcardS] using K.index_dvd_card
      rw [←hdegree,he] at hd
      exact (by decide : ¬(9:ℕ)∣168) hd
    by_cases htiny : c=2 ∧ Nat.card X<10
    · have hsmall : Nat.card X=7 ∨ Nat.card X=8 := by omega
      exact SmallFibreOrder168BinaryClassGap.binary_seven_eight_subnormal_class_cube_gap
        π hπ (fun x=>(hsize x).trans htiny.1) E hcardS houter hB hk hsmall H hH
    · have htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
          Nat.card (ConjClasses L)≤12 := by
        intro L hL
        exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hB
      have hlocal : ∀x (L:Subgroup (Equiv.Perm (originalBlockFibre π x))),
          Nat.card (ConjClasses L)≤c := by
        rcases hc with rfl|rfl
        · exact fun x L=>SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
        · exact fun x L=>SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
      have hbound := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
        π hπ c hlocal 12 htop H hH
      have hnum : (c^Nat.card X*12)^3≤5^(c*Nat.card X-2) := by
        rcases hc with rfl|rfl
        · exact SmallFibreTwelveClassEnvelope.binary_gap (Nat.card X) (by omega)
        · exact SmallFibreTwelveClassEnvelope.ternary_gap (Nat.card X) hn
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π c hsize
      have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
      simpa only [hcard,Nat.mul_comm (Nat.card X) c] using hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoSevenClassGap
