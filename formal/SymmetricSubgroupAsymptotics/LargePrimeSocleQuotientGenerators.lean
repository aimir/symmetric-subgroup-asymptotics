import SymmetricSubgroupAsymptotics.SingleCycleNormalizerQuotientGenerators
import SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG
import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow
import SymmetricSubgroupAsymptotics.PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput
import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorOrdinaryRecurrence

/-! Frattini's actual normalizer supplement bounds the SAME original
socle quotient from a large prime cycle. Its fixed-point action receives
the independently proved all-subgroups degree10 budget. No full Outer
order or simple index-square bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LargePrimeSocleQuotientGenerators
open SingleCycleNormalizerQuotientGenerators
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] {p : ℕ} [Fact p.Prime]

theorem quotient_genRank_le_fixedBudget (hCFSG : CFSG.CFSGClassification)
    (S : Subgroup G) [S.Normal] (hpdiv : p ∣ Nat.card S)
    (hnot : ¬p^2 ∣ Nat.card S) (hdegree : Nat.card X<2*p)
    (hfixed : Nat.card X-p ≤ 10) :
    MarkedC4.genRank (G ⧸ S) ≤ 1+TenPointHalfDegreeCompleteCFSG.fixedBudget (Nat.card X-p) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := S) p hpdiv
  have hU : IsPGroup p (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ha,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have haP : a ∈ P := hP (Subgroup.mem_zpowers a)
  have hPcard : Nat.card P=p :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P a haP ha hnot
  have hPgen : (P : Subgroup S)=Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hP (by rw [Nat.card_zpowers,ha,hPcard])).symm
  let H : Subgroup G := (P : Subgroup S).map S.subtype
  have hHgen : H=Subgroup.zpowers (a : G) := by
    dsimp only [H]
    rw [hPgen,MonoidHom.map_zpowers]
    rfl
  have hHcard : Nat.card H=p := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    exact hPcard
  letI : IsCyclic (MulAut H) := cyclic_aut_of_prime_card H p hHcard
  let rho : G →* Equiv.Perm X := MulAction.toPermHom G X
  have horder : orderOf (rho (a : G))=p :=
    (orderOf_injective rho MulAction.toPerm_injective (a : G)).trans
      ((Subgroup.orderOf_coe a).trans ha)
  letI : Fintype X := Fintype.ofFinite X
  have hc : (rho (a : G)).IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [horder]; exact Fact.out) (by rw [horder,←Nat.card_eq_fintype_card]; exact hdegree)
  have htype : (rho (a : G)).cycleType={p} := by
    rw [hc.cycleType,←hc.orderOf,horder]
  let beta : Normalizer H →* G ⧸ S :=
    (QuotientGroup.mk' S).comp (Subgroup.normalizer (H : Set G)).subtype
  have hbeta : Function.Surjective beta := by
    apply MonoidHom.range_eq_top.mp
    change ((QuotientGroup.mk' S).comp (Subgroup.normalizer (H : Set G)).subtype).range=⊤
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
    have hcod : Codisjoint (Subgroup.normalizer (H : Set G)) (QuotientGroup.mk' S).ker := by
      rw [QuotientGroup.ker_mk']
      exact codisjoint_iff.mpr (Sylow.normalizer_sup_eq_top P)
    rw [(Subgroup.map_eq_range_iff).mpr hcod]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective S)
  have hHleS : H ≤ S := by
    rintro g ⟨b,hb,rfl⟩
    exact b.property
  have hkill : H.subgroupOf (Normalizer H) ≤ beta.ker := by
    intro u hu
    change u.val ∈ (QuotientGroup.mk' S).ker
    rw [QuotientGroup.ker_mk']
    exact hHleS hu
  have hcard : Nat.card (Fixed (X := X) H)=Nat.card X-p := fixed_card H (a : G) hHgen p htype
  have hb := TenPointHalfDegreeCompleteCFSG.faithful_genRank_le_fixedBudget hCFSG
    (G := (fixedHom (X := X) H).range) (X := Fixed (X := X) H)
    (by rw [hcard]; exact hfixed)
  rw [hcard] at hb
  exact quotient_genRank_le_one_add (X := X) H (a : G) hHgen hc beta hbeta hkill _ hb

/-- The original one-factor socle is forced by raw degree geometry below25,
independently of any expected simple-model order or index-square theorem. -/
theorem nonaffine_genRank_le_fixedBudget (hCFSG : CFSG.CFSGClassification)
    (D : NonaffineData G X) (hsmall : Nat.card X<25)
    (hhead : MarkedC4.genRank D.Simple ≤ 2) (hpdiv : p ∣ Nat.card D.Simple)
    (hnot : ¬p^2 ∣ Nat.card D.Simple) (hdegree : Nat.card X<2*p)
    (hfixed : Nat.card X-p ≤ 10) :
    MarkedC4.genRank G ≤ 3+TenPointHalfDegreeCompleteCFSG.fixedBudget (Nat.card X-p) := by
  have hk := PrimitiveSocleBelowTwentyFiveSingleFactorWithoutIndexInput.factorCount_eq_one D hsmall
  have hcard : Nat.card (finiteGroupSocle G)=Nat.card D.Simple :=
    Nat.card_congr (D.oneFactorEquiv hk).toEquiv
  have hQ := quotient_genRank_le_fixedBudget (p := p) (X := X) hCFSG (finiteGroupSocle G)
    (by rw [hcard]; exact hpdiv) (by rw [hcard]; exact hnot) hdegree hfixed
  have hG := PrimitiveSocleOneFactorOrdinaryRecurrence.genRank_le_simple_add_actual_quotient D hk
  omega

end SymmetricSubgroupAsymptotics.LargePrimeSocleQuotientGenerators
