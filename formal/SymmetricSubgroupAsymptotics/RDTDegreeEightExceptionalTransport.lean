import SymmetricSubgroupAsymptotics.MarkedC4RDTDegreeEightExceptional
import SymmetricSubgroupAsymptotics.MarkedC4ActualMarkZeroNormalRank
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Transport and quotient recognition for the binary degree-eight exception

Normal generator numbers and the exact centralizer/commutator invariants
are transported through the same group equivalence. A group whose centre
and derived subgroup coincide and have prime order has only abelian
nontrivial normal quotients. The degree-eight application uses prime two.
No classification or numerical bound is assumed by these transport lemmas.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalTransport

open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel
open MarkedC4.RDTNormalFInterface

variable {G H : Type} [Group G] [Group H]

theorem normalGen_map_equiv [Finite G] [Finite H]
    (e : G ≃* H) (N : Subgroup G) [N.Normal] :
    normalGen (N.map e.toMonoidHom) = normalGen N := by
  exact MarkedC4.ActualMarkZeroNormalRank.normalGen_map_eq
    e.toMonoidHom e.surjective N (fun x _ hx => e.injective (by simpa using hx))

theorem hasExcess_of_equiv [Finite G] [Finite H]
    (e : G ≃* H) {n i : ℕ} (h : HasExcess G n i) : HasExcess H n i := by
  constructor
  · obtain ⟨N, hN, hval⟩ := h.1
    letI : N.Normal := hN
    letI : (N.map e.toMonoidHom).Normal :=
      Subgroup.Normal.map hN e.toMonoidHom e.surjective
    exact ⟨N.map e.toMonoidHom, inferInstance, by rw [normalGen_map_equiv]; exact hval⟩
  · intro N hN
    letI : N.Normal := hN
    have hback := h.2 (N.map e.symm.toMonoidHom)
      (Subgroup.Normal.map hN e.symm.toMonoidHom e.symm.surjective)
    rwa [normalGen_map_equiv e.symm N] at hback

def centerEquiv (e : G ≃* H) : Subgroup.center G ≃* Subgroup.center H where
  toFun g := ⟨e g, by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨x, rfl⟩ := e.surjective h
    exact (e.map_mul x g).symm.trans
      ((congrArg e (Subgroup.mem_center_iff.mp g.property x)).trans (e.map_mul g x))⟩
  invFun h := ⟨e.symm h, by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp h.property (e g)⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g)
  right_inv h := Subtype.ext (e.apply_symm_apply h)
  map_mul' g h := Subtype.ext (e.map_mul g h)

def derivedEquiv (e : G ≃* H) : commutator G ≃* commutator H :=
  (e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl))

theorem centralLog_top_equiv [Finite G] [Finite H] (e : G ≃* H) :
    centralLog (⊤ : Subgroup G) = centralLog (⊤ : Subgroup H) := by
  simp only [centralLog, targetCentralizer, Subgroup.coe_top,
    Subgroup.centralizer_univ]
  rw [Nat.card_congr (centerEquiv e).toEquiv]

theorem commutatorLog_top_equiv [Finite G] [Finite H] (e : G ≃* H) :
    commutatorLog (⊤ : Subgroup G) = commutatorLog (⊤ : Subgroup H) := by
  change Real.logb 2 (Nat.card (commutator G)) =
    Real.logb 2 (Nat.card (commutator H))
  rw [Nat.card_congr (derivedEquiv e).toEquiv]

theorem subgroup_eq_bot_or_prime_subgroup
    (D N : Subgroup G) (hD : (Nat.card D).Prime) (hND : N ≤ D) :
    N = ⊥ ∨ N = D := by
  letI : Fact (Nat.card D).Prime := ⟨hD⟩
  rcases (N.subgroupOf D).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    have hm := congrArg (fun K : Subgroup D => K.map D.subtype) h
    simpa only [Subgroup.map_subgroupOf_eq_of_le hND, Subgroup.map_bot] using hm
  · right
    have hm := congrArg (fun K : Subgroup D => K.map D.subtype) h
    simpa only [Subgroup.map_subgroupOf_eq_of_le hND,
      ← MonoidHom.range_eq_map, D.range_subtype] using hm

/-- The extraspecial quotient implication uses the literal derived
subgroup and centre, rather than a classification label or quotient census. -/
theorem normal_eq_bot_of_nonabelian_quotient
    (hderived : commutator G = Subgroup.center G)
    (hprime : (Nat.card (commutator G)).Prime)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ x y : G ⧸ N, x * y = y * x) : N = ⊥ := by
  have hnot : ¬ commutator G ≤ N := by
    intro hle
    have hc := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
    exact hnonab (fun x y => hc.is_comm.comm x y)
  have hdis : N ⊓ commutator G = ⊥ := by
    rcases subgroup_eq_bot_or_prime_subgroup (commutator G)
      (N ⊓ commutator G) hprime inf_le_right with hh | hh
    · exact hh
    · exact False.elim (hnot (hh.symm ▸ inf_le_left))
  have hcentral : N ≤ Subgroup.center G := by
    rw [← Subgroup.centralizer_univ]
    change N ≤ Subgroup.centralizer ((⊤ : Subgroup G) : Set G)
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf (Subgroup.commutator_le_left N ⊤)
      (Subgroup.commutator_mono le_top le_rfl)
  rcases subgroup_eq_bot_or_prime_subgroup (commutator G) N hprime
    (hcentral.trans_eq hderived.symm) with h | h
  · exact h
  · exact False.elim (hnot (h ▸ le_rfl))

/-- Exact binary packet after identifying an actual source with its model. -/
theorem quotient_packet_of_equiv [Finite G] [Finite H]
    (e : G ≃* H)
    (hderived : commutator H = Subgroup.center H)
    (hcard : Nat.card (commutator H) = 2)
    (N : Subgroup G) [N.Normal]
    (hnonab : ¬ ∀ x y : G ⧸ N, x * y = y * x) :
    N = ⊥ ∧ centralLog (⊤ : Subgroup (G ⧸ N)) = 1 ∧
      commutatorLog (⊤ : Subgroup (G ⧸ N)) +
        3 * centralLog (⊤ : Subgroup (G ⧸ N)) = 4 := by
  let M := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  let q := QuotientGroup.congr N M e rfl
  have hMnonab : ¬ ∀ x y : H ⧸ M, x * y = y * x := by
    intro h
    apply hnonab
    intro x y
    apply q.injective
    simpa only [map_mul] using h (q x) (q y)
  have hM : M = ⊥ := normal_eq_bot_of_nonabelian_quotient hderived
    (hcard ▸ Nat.prime_two) M hMnonab
  have hN : N = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ M := ⟨x, hx, rfl⟩
    rw [hM, Subgroup.mem_bot] at he
    exact e.injective (by simpa using he)
  subst N
  let eq : (G ⧸ (⊥ : Subgroup G)) ≃* H := (QuotientGroup.quotientBot).trans e
  have hc : centralLog (⊤ : Subgroup H) = 1 := by
    simp only [centralLog, targetCentralizer, Subgroup.coe_top,
      Subgroup.centralizer_univ, ← hderived, hcard, Nat.cast_ofNat]
    norm_num
  have hd : commutatorLog (⊤ : Subgroup H) = 1 := by
    change Real.logb 2 (Nat.card (commutator H)) = 1
    rw [hcard]
    norm_num
  rw [centralLog_top_equiv eq, commutatorLog_top_equiv eq, hc, hd]
  norm_num

end SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalTransport

end
