import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingKernelPartition
import SymmetricSubgroupAsymptotics.RankOneCubicSylowCentralizer
import SymmetricSubgroupAsymptotics.BinaryThreeQuartetLiteralSocles

/-! Actual commutators lift the regular Klein block group while
centralizing a rank-one odd kernel. Global inversion of the cubic line
is allowed: its automorphism group is abelian, so commutators kill it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerCommutators
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneWreathActualOddKernel
abbrev R := BinaryRegularKleinWreath.R
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

def label : R ≃ Fin 4 :=
  Multiplicative.toAdd.trans BinaryThreeQuartetLiteralSocles.planeLabel

def regular : R →* Equiv.Perm (Fin 4) :=
  label.permCongrHom.toMonoidHom.comp (MulAction.toPermHom R R)

theorem regular_injective : Function.Injective regular :=
  label.permCongrHom.injective.comp MulAction.toPerm_injective

private def triples (j : Fin 8) : Equiv.Perm (Fin 4) :=
  let a := TernaryFourBlockPermutationGenerators.a
  let b := TernaryFourBlockPermutationGenerators.b
  ![a,a⁻¹,b,b⁻¹,b*a*b⁻¹,b*a⁻¹*b⁻¹,b^2*a*(b^2)⁻¹,b^2*a⁻¹*(b^2)⁻¹] j

private theorem triples_even : ∀ j, triples j∈alternatingGroup (Fin 4) := by
  change ∀ j, Equiv.Perm.sign (triples j)=1
  decide +kernel

private theorem commutator_cover : ∀ r : R, ∃ i j : Fin 8,
    triples i*triples j*(triples i)⁻¹*(triples j)⁻¹=regular r := by decide +kernel

private theorem automorphisms_commute {O : Type} [Group O] [Finite O]
    (e : O ≃* Cubic) (g h : MulAut O) : g*h=h*g := by
  have hsmall := RankOneCubicSylowCentralizer.automorphism_card_le_two e
  have hpos : 0<Nat.card (MulAut O) := Nat.card_pos
  have hc : Nat.card (MulAut O)=1 ∨ Nat.card (MulAut O)=2 := by omega
  rcases hc with hc | hc
  · letI : Subsingleton (MulAut O) := (Nat.card_eq_one_iff_unique.mp hc).1
    exact Subsingleton.elim _ _
  · letI : Fact (Nat.Prime 2) := ⟨by decide⟩
    letI : IsCyclic (MulAut O) := isCyclic_of_prime_card hc
    letI : CommGroup (MulAut O) := IsCyclic.commGroup
    exact mul_comm g h

variable (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

def top : C →* Equiv.Perm (Fin 4) := PermutationalWreathProduct.rightHom.comp C.subtype

include e in
theorem commutator_centralizes (g h : C) (o : oddKernel C) :
    Commute (g*h*g⁻¹*h⁻¹) (o : C) := by
  let a : C →* MulAut (oddKernel C) := MulAut.conjNormal
  have ha : a (g*h*g⁻¹*h⁻¹)=1 := by
    simp only [map_mul,map_inv]
    rw [automorphisms_commute e (a g) (a h)]
    group
  have hc := congrArg (fun f : MulAut (oddKernel C) => (f o : C)) ha
  change (g*h*g⁻¹*h⁻¹)*(o : C)*(g*h*g⁻¹*h⁻¹)⁻¹=(o : C) at hc
  exact mul_inv_eq_iff_eq_mul.mp hc

include e heven in
/-- Actual block lifts centralizing K, without a splitting of C or of
any original affine extension. -/
theorem exists_regular_centralizing_lift (r : R) :
    ∃ h : C, top C h=regular r ∧ ∀ o : oddKernel C, Commute h (o : C) := by
  obtain ⟨i,j,hij⟩ := commutator_cover r
  obtain ⟨g,hg⟩ := heven ⟨triples i,triples_even i⟩
  obtain ⟨h,hh⟩ := heven ⟨triples j,triples_even j⟩
  refine ⟨g*h*g⁻¹*h⁻¹,?_,commutator_centralizes C e g h⟩
  change top C g=triples i at hg
  change top C h=triples j at hh
  simpa only [map_mul,map_inv,hg,hh] using hij

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingCentralizerCommutators
