import SymmetricSubgroupAsymptotics.ProductQuartetAlternatingNonzeroSocles
import SymmetricSubgroupAsymptotics.ProductQuartetCyclicTopNonbinarySocles
import SymmetricSubgroupAsymptotics.ProductQuartetBinaryTopNonbinarySocles
import SymmetricSubgroupAsymptotics.TransitiveFourBinaryOrAlternating
import SymmetricSubgroupAsymptotics.TransitiveRegularBlockChart
import SymmetricSubgroupAsymptotics.CardFourCyclicOrKleinChart
import SymmetricSubgroupAsymptotics.DihedralEightActualBlockChart
import SymmetricSubgroupAsymptotics.ProductBlockFrameTransitiveTop

/-! No-premise dispatch of the actual transitive four-point coarse top.
The cyclic, regular-Klein, dihedral and alternating charts exhaust its
possible orders. No row catalogue, normal census or socle callback occurs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
local instance quartetNonzeroFactTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev R := BinaryRegularKleinWreath.R
local instance quartetNonzeroKleinFintype : Fintype R := BinaryRegularKleinWreath.rFintype
local instance quartetNonzeroKleinDecidableEq : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem kleinR : IsKleinFour R := by
  refine ⟨by simp [R,BinaryRegularKleinWreath.R,Nat.card_eq_fintype_card],?_⟩
  apply (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
  intro g hg
  apply orderOf_eq_prime (p := 2) _ hg
  exact (by decide +kernel : ∀ r : R,r^2=1) g

private theorem not_binary_of_three_dvd {G : Type} [Group G] [Finite G]
    (h3 : 3∣Nat.card G) : ¬IsPGroup 2 G := by
  intro hp
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [hn] at h3
  have h32 : 3∣2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

variable {X : Type} [Finite X] {T : Subgroup (Equiv.Perm X)}
  (C : ProductBlockFrame T (Fin 4) Plane)

 theorem nonzero_odd_nonbinary_quotientSocle [MulAction.IsPretransitive T X]
    (hO : oddKernel C.quartetLinearImage≠⊥)
    (N : Subgroup T) [N.Normal] (hQ : ¬ IsPGroup 2 (T ⧸ N)) :
    SocleNormalGeneratorBound (T ⧸ N) 2 := by
  let B := C.top.range
  letI : Fintype B := Fintype.ofFinite B
  have htrans : ∀ i k : Fin 4,∃ b : B,(b : Equiv.Perm (Fin 4)) i=k :=
    C.top_range_transitive (fun x y => MulAction.exists_smul_eq T x y)
  rcases TransitiveFourBinaryOrAlternating.card_cases B htrans with h4 | h8 | h12 | h24
  · rcases CardFourCyclicOrKleinChart.cyclic_or_klein h4 with hcyc | hklein
    · letI : IsCyclic B := hcyc
      obtain ⟨g,hgen⟩ := IsCyclic.exists_generator (α := B)
      have hcycle : ∀ i : Fin 4,∃ n : ℕ,g^n • (0 : Fin 4)=i := by
        intro i
        obtain ⟨b,hb⟩ := htrans 0 i
        obtain ⟨n,hn⟩ := (finEquivZPowers (isOfFinOrder_of_finite g)).surjective ⟨b,hgen b⟩
        refine ⟨n.val,?_⟩
        have he : g^n.val=b := congrArg Subtype.val hn
        rw [he]
        exact hb
      have hB : IsPGroup 2 B := IsPGroup.of_card (n := 2) (by simpa using h4)
      exact C.cyclic_nonbinary_quotientSocle (MulEquiv.refl B) (Equiv.refl (Fin 4))
        (fun _ _ => rfl) g 0 hcycle hB N hQ
    · letI : IsKleinFour B := hklein
      letI : IsKleinFour R := kleinR
      obtain ⟨e⟩ := (IsKleinFour.nonempty_mulEquiv : Nonempty (B ≃* R))
      have hcard : Fintype.card B=Fintype.card (Fin 4) := by
        simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h4
      let c := TransitiveRegularBlockChart.chart (0 : Fin 4) (htrans 0) hcard e
      exact C.klein_nonbinary_quotientSocle e c
        (TransitiveRegularBlockChart.chart_equivariant (0 : Fin 4) (htrans 0) hcard e) N hQ
  · obtain ⟨e,c,hc⟩ := DihedralEightActualBlockChart.exists_chart B h8
    exact C.dihedral_nonbinary_quotientSocle e c hc N hQ
  · have hn : ¬IsPGroup 2 B := not_binary_of_three_dvd (by rw [h12]; decide)
    have heven := (TransitiveFourBinaryOrAlternating.binary_or_alternating B htrans).resolve_left hn
    exact QuartetKernel.alternating_nonzero_quotientSocle C hO heven N
  · have hn : ¬IsPGroup 2 B := not_binary_of_three_dvd (by rw [h24]; decide)
    have heven := (TransitiveFourBinaryOrAlternating.binary_or_alternating B htrans).resolve_left hn
    exact QuartetKernel.alternating_nonzero_quotientSocle C hO heven N

end SymmetricSubgroupAsymptotics.ProductBlockFrame
