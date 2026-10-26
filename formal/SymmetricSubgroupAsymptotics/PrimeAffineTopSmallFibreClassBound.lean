import SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreNumerics
import SymmetricSubgroupAsymptotics.PrimeDegreeAffineAllSubgroupsClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineHeadOrderBudget
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedGeneralClassReserve
import SymmetricSubgroupAsymptotics.QuasiprimitiveSwapRecognition
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction

/-! Every actual prime-degree affine top of degree at least five pays
the ordinary binary/ternary block bound. Its subgroups receive the proved
prime-kernel Frobenius class bound. The binary degree-five endpoint uses
the actual unsigned kernel reserve; it is not enlarged to a full wreath. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreClassBound
open OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem subnormal_class_cube_le_of_prime_affine_top
    (π : Ω → X) (hπ : ∀ (g : A) (ω : Ω), π (g • ω)=g • π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀ x, Nat.card (originalBlockFibre π x)=c)
    (hp : (Nat.card X).Prime) (hn : 5 ≤ Nat.card X)
    (P : PrimitiveAffineProfile (Top (A:=A) (X:=X)) X)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-1) := by
  letI : Nonempty X := Finite.card_pos_iff.mp (by omega)
  let x₀ : X := Classical.arbitrary X
  have htop : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
      Nat.card (ConjClasses L) ≤ Nat.card X :=
    fun L _ => PrimeDegreeAffineAllSubgroupsClassBound.subgroup_class_card_le_degree P x₀ hp L
  rcases hc with rfl | rfl
  · by_cases he : Nat.card X=5
    · letI : Fintype X := Fintype.ofFinite X
      letI : DecidableEq X := Classical.decEq X
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      letI : MulAction.IsPretransitive (Top (A:=A) (X:=X)) X :=
        ⟨fun x y => by
          obtain ⟨v,hv,_⟩ := P.regular x y
          exact ⟨v.val,hv⟩⟩
      letI : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X :=
        MulAction.IsPreprimitive.of_prime_card hp
      have ho : Nat.card (Top (A:=A) (X:=X)) ≤ 25 := by
        simpa only [he] using P.card_le_degree_sq_of_degree_prime
          (inferInstance : MulAction.IsPreprimitive (Top (A:=A) (X:=X)) X) hp
      have hns : ∀ a:A, ¬(topMap (A:=A) (X:=X) a).IsSwap := by
        intro a ha
        have ht : Top (A:=A) (X:=X)=⊤ :=
          QuasiprimitiveSwapRecognition.eq_top_of_isSwap_mem
            (Top (A:=A) (X:=X)) (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
        have hs : Nat.card (Top (A:=A) (X:=X))=120 := by
          rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm,he]
          decide
        omega
      have ht11 : ∀ L : Subgroup (Top (A:=A) (X:=X)), L.IsSubnormal →
          Nat.card (ConjClasses L) ≤ 11 := by
        intro L hL
        have hh := htop L hL
        omega
      have hb := BinaryBlockUnsignedGeneralClassReserve.subnormal_class_card_le_class_budget_add_one_mul
        π hπ (fun x => (hsize x).le) (by omega) 11 (by decide) ht11 hns H hH
      have hh := Nat.pow_le_pow_left hb 3
      rw [he] at hh
      have hh' := hh.trans PrimeAffineTopSmallFibreNumerics.binary_unsigned_five
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
      simpa only [hcard,he] using hh'
    · have hn7 : 7 ≤ Nat.card X := by
        by_contra h
        have he6 : Nat.card X=6 := by omega
        rw [he6] at hp
        norm_num at hp
      have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
          Nat.card (ConjClasses L) ≤ 2 :=
        fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_two (hsize x).le L
      have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
        π hπ 2 hlocal (Nat.card X) htop H hH
      have hh := (Nat.pow_le_pow_left hb 3).trans
        (PrimeAffineTopSmallFibreNumerics.binary_degree_tail (Nat.card X) hn7)
      have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
      simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh
  · have hlocal : ∀ x (L : Subgroup (Equiv.Perm (originalBlockFibre π x))),
        Nat.card (ConjClasses L) ≤ 3 :=
      fun x L => SmallPermutationClassBudgets.subgroup_class_card_le_three (hsize x).le L
    have hb := SubnormalSmallFibreTopClassBound.subnormal_class_card_le_power_mul_top_budget
      π hπ 3 hlocal (Nat.card X) htop H hH
    have hh := (Nat.pow_le_pow_left hb 3).trans
      (PrimeAffineTopSmallFibreNumerics.ternary_degree_tail (Nat.card X) hn)
    have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 3 hsize
    simpa only [hcard,Nat.mul_comm (Nat.card X) 3] using hh

end SymmetricSubgroupAsymptotics.PrimeAffineTopSmallFibreClassBound
