import SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalGapNumerics
import SymmetricSubgroupAsymptotics.PrimitiveAlternatingSubnormalPartitionWreath
import SymmetricSubgroupAsymptotics.LargeTopFiniteModelResidual

/-! A one-power class-cube saving for subnormal subgroups of large
primitive groups. Full-group order bounds control subgroup orders;
alternating components use the actual subnormal wreath class theorem.
The only residual sources are literal Tits and sporadic models, with
the original D/K and both failed order budgets retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalClassGap
open PrimitiveSocleRawStructure LargePrimitiveSubnormalGapNumerics
open LargeTopFiniteModelResidual

theorem subgroup_cube_gap_of_order (G : Type) [Group G] [Finite G]
    (n : ℕ) (hn : 4096 ≤ n)
    (horder : Nat.card G ≤ n ^ (4 * Nat.log 2 n + 30)) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (n - 2) := by
  have hc : Nat.card (ConjClasses H) ≤ Nat.card G :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk H _) ConjClasses.mk_surjective).trans
      (Nat.card_le_card_of_injective (fun x : H => x.val) Subtype.val_injective)
  apply cube_gap_of_binary_product n _ (by omega)
  exact (Nat.pow_le_pow_left (Nat.mul_le_mul_left (2 ^ n) hc) 3).trans
    (LargePrimitiveWideSmallFibreClassNumerics.binary_product_cube_le n (Nat.card G) hn horder)

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem alternating_subnormal_cube_gap
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m))
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X = K.index ^ D.factorCount)
    (hn : 4096 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) := by
  have hclass := D.subnormal_class_card_le_partition_wreath m hm e H hH
  have hell := CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)
  apply cube_gap_of_binary_product (Nat.card X) _ (by omega)
  by_cases hk : 2 ≤ D.factorCount
  · have hmlower : m ^ D.factorCount ≤ Nat.card X :=
      (Nat.pow_le_pow_left (hell.2 K hK) _).trans_eq hdegree.symm
    have hcap : Nat.card (ConjClasses H) ≤
        (8 * 2 ^ m) ^ D.factorCount * D.factorCount.factorial :=
      hclass.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
        (Nat.mul_le_mul_left 8 (BinaryPartitionBudget.partition_card_le_power m)) _))
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_left (2 ^ Nat.card X) hcap) 3).trans
      (AlternatingMultiFactorSmallFibreClassNumerics.binary_product_cube_le
        m D.factorCount (Nat.card X) hm hk hn hmlower)
  · have hk1 : D.factorCount = 1 := by have hh := D.factorCount_pos; omega
    have hd : Nat.card X = K.index := by simpa only [hk1,pow_one] using hdegree
    have hmb := (hell.2 K hK).trans_eq hd.symm
    have hp := PartitionFiveSeparatedEncoding.partition_card_le_separated m
    have hmono : (m + 1) ^ 4 * 6 ^ ((m + 4) / 5) ≤
        (Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.succ_le_succ hmb) 4)
        (Nat.pow_le_pow_right (by decide : 0 < (6 : ℕ))
          (Nat.div_le_div_right (Nat.add_le_add_right hmb 4)))
    have hc0 : Nat.card (ConjClasses H) ≤ 8 * Nat.card (Nat.Partition m) := by
      simpa only [hk1,pow_one,Nat.factorial_one,mul_one] using hclass
    have hcap := hc0.trans (Nat.mul_le_mul_left 8 (hp.trans hmono))
    have hw : 2 ^ Nat.card X * Nat.card (ConjClasses H) ≤
        2 ^ Nat.card X * 8 * (Nat.card X + 1) ^ 4 * 6 ^ ((Nat.card X + 4) / 5) :=
      (Nat.mul_le_mul_left _ hcap).trans_eq (by ac_rfl)
    exact (Nat.pow_le_pow_left hw 3).trans
      (AlternatingSmallFibrePartitionTailNumerics.binary_partition_envelope_cube_le (Nat.card X) hn)

private theorem alternating_of_remaining_not_finite (i : CFSG.Index)
    (hi : CFSGModelComponentIndexOrderBudget.RemainingSimpleType i)
    (hf : ¬ RemainingFiniteSimpleType i) :
    ∃ (m : ℕ) (hm : 5 ≤ m), i = .alternating m hm := by
  cases i <;> simp_all [CFSGModelComponentIndexOrderBudget.RemainingSimpleType,
    RemainingFiniteSimpleType]

theorem primitive_subnormal_cube_gap_or_actual_finite_model
    [FaithfulSMul G X] (hCFSG : CFSG.CFSGClassification)
    (hprimitive : MulAction.IsPreprimitive G X) (hn : 4096 ≤ Nat.card X)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 2) ∨
      ∃ D : NonaffineData G X,
        ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPreprimitive G X := hprimitive
  obtain ⟨P⟩ := publishedONanScottStructure G X
  cases P with
  | inr P =>
    left
    apply subgroup_cube_gap_of_order G (Nat.card X) hn _ H
    calc
      Nat.card G ≤ Nat.card X * Nat.card X ^ Nat.log 2 (Nat.card X) :=
        P.card_le_domain_pow_log (Classical.choice inferInstance)
      _ = Nat.card X ^ (Nat.log 2 (Nat.card X) + 1) := by rw [pow_succ,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  | inl D =>
    rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
    · by_cases hlog : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤
          K.index ^ (4 * Nat.log 2 K.index + 23)
      · exact Or.inl (subgroup_cube_gap_of_order G (Nat.card X) hn
          ((D.card_le_log_order_of_index_form K hK hdegree hlog).trans
            (Nat.pow_le_pow_right (by omega) (by omega))) H)
      · by_cases hbound : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66
        · have hlogn : 12 ≤ Nat.log 2 (Nat.card X) :=
            Nat.le_log_of_pow_le (by decide)
              (show 2 ^ 12 ≤ Nat.card X by
                simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using hn)
          exact Or.inl (subgroup_cube_gap_of_order G (Nat.card X) hn
            ((D.card_le_degree_pow_bounded_component K hK hdegree hbound).trans
              (Nat.pow_le_pow_right (by omega) (by omega))) H)
        · rcases CFSGModelComponentIndexOrderBudget.simple_budget_or_actual_remaining_model
            hCFSG D.Simple D.noncommutative with hb | ⟨i,hi,he⟩
          · rcases hb K hK with hb | hb
            · exact (hlog hb).elim
            · exact (hbound hb).elim
          · by_cases hf : RemainingFiniteSimpleType i
            · exact Or.inr ⟨D,i,hf,he,K,hK,hdegree,lt_of_not_ge hlog,lt_of_not_ge hbound⟩
            · obtain ⟨m,hm,rfl⟩ := alternating_of_remaining_not_finite i hi hf
              obtain ⟨e⟩ := he
              exact Or.inl (alternating_subnormal_cube_gap D m hm e K hK hdegree hn H hH)
    · exact Or.inl (subgroup_cube_gap_of_order G (Nat.card X) hn
        ((D.card_le_degree_pow_log_of_power_form a hka hdegree (by omega)).trans
          (Nat.pow_le_pow_right (by omega) (by omega))) H)

end SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalClassGap
