import SymmetricSubgroupAsymptotics.CanonicalLifts
import SymmetricSubgroupAsymptotics.ComplementCount
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Order.LatticeIntervals
import Mathlib.GroupTheory.Frattini

/-!
# The square condition and actual lift fibres

The fibre consists of literal subgroups, with prescribed image and kernel
intersection. The square condition, rather than merely a commutator
condition, makes the relevant quotient a binary vector space. Its subgroups
are then identified with linear subspaces and the lift fibre with complements.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G Q : Type*} [Group G] [Group Q]

/-- The actual subgroup fibre over the full quotient, with prescribed kernel
intersection. A subspace image is handled by restricting to its preimage. -/
def SquareLiftFibre (π : G →* Q) (W : Subgroup G) :=
  {H : Subgroup G // H.map π = ⊤ ∧ H ⊓ π.ker = W}

/-- Full image is the exact lattice condition with the quotient kernel. -/
theorem map_eq_top_iff_sup_kernel (π : G →* Q) (hπ : Function.Surjective π)
    (H : Subgroup G) : H.map π = ⊤ ↔ H ⊔ π.ker = ⊤ := by
  rw [← (Subgroup.comap_injective hπ).eq_iff, Subgroup.comap_map_eq,
    Subgroup.comap_top]

/-- Every subgroup of a central kernel is normal in the ambient group. -/
theorem normal_of_le_central_kernel (π : G →* Q) (hcentral : π.ker ≤ Subgroup.center G)
    (W : Subgroup G) (hW : W ≤ π.ker) : W.Normal where
  conj_mem n hn g := by
    have hc := Subgroup.mem_center_iff.mp (hcentral (hW hn)) g
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hn

/-- Necessity retains all squares above the chosen image. Centrality and the
kernel's exponent-two property make the square independent of its lift. -/
theorem squares_mem_of_lift (π : G →* Q)
    (hcentral : π.ker ≤ Subgroup.center G)
    (hkernel : ∀ g ∈ π.ker, g ^ 2 = 1) (hquotient : ∀ q : Q, q ^ 2 = 1)
    (W H : Subgroup G) (himage : H.map π = ⊤) (hinter : H ⊓ π.ker = W) :
    ∀ g : G, g ^ 2 ∈ W := by
  intro g
  have hg : π g ∈ H.map π := by rw [himage]; trivial
  obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.mp hg
  let k := h⁻¹ * g
  have hk : k ∈ π.ker := by
    change π (h⁻¹ * g) = 1
    simp [hhg]
  have hc : Commute h k := Subgroup.mem_center_iff.mp (hcentral hk) h
  have hgk : g = h * k := by simp [k]
  have hh2 : h ^ 2 ∈ W := by
    rw [← hinter]
    exact ⟨H.pow_mem hh 2, by change π (h ^ 2) = 1; simpa using hquotient (π h)⟩
  rw [hgk, hc.mul_pow, hkernel k hk, mul_one]
  exact hh2

private def liftIntervalEquiv (π : G →* Q) (hπ : Function.Surjective π)
    (W : Subgroup G) (hW : W ≤ π.ker) :
    SquareLiftFibre π W ≃
      {H : Set.Ici W // IsCompl (⟨π.ker, hW⟩ : Set.Ici W) H} where
  toFun H := ⟨⟨H.1, by exact H.2.2.ge.trans inf_le_left⟩, by
    rw [Set.Ici.isCompl_iff, codisjoint_iff]
    exact ⟨by simpa [inf_comm] using H.2.2,
      by simpa [sup_comm] using (map_eq_top_iff_sup_kernel π hπ H.1).mp H.2.1⟩⟩
  invFun H := ⟨H.1.1, by
    have h := Set.Ici.isCompl_iff.mp H.2
    exact ⟨(map_eq_top_iff_sup_kernel π hπ H.1.1).mpr
      (by simpa [codisjoint_iff, sup_comm] using h.2),
      by simpa [inf_comm] using h.1⟩⟩
  left_inv H := rfl
  right_inv H := rfl

/-- The correspondence between actual lifts and quotient subgroup
complements is valid before any square or commutativity assumption. -/
def quotientLiftComplementEquiv (π : G →* Q) (hπ : Function.Surjective π)
    (W : Subgroup G) [W.Normal] (hW : W ≤ π.ker) :
    SquareLiftFibre π W ≃
      {L : Subgroup (G ⧸ W) // IsCompl (π.ker.map (QuotientGroup.mk' W)) L} :=
  (liftIntervalEquiv π hπ W hW).trans
    ((QuotientGroup.comapMk'OrderIso W).symm.toEquiv.subtypeEquiv (fun H => by
      simpa using (QuotientGroup.comapMk'OrderIso W).symm.isCompl_iff
        (x := (⟨π.ker, hW⟩ : Set.Ici W)) (y := H)))

/-- In any group, the identity of all squares forces commutativity. This is
the polarization step and needs no separate commutator assumption. -/
theorem mul_comm_of_all_squares_one {X : Type*} [Group X]
    (hsquare : ∀ x : X, x ^ 2 = 1) (x y : X) : x * y = y * x := by
  have hinv (z : X) : z⁻¹ = z :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare z)
  calc
    x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hinv, hinv]

/-- The square condition is exactly what makes every quotient element have
order dividing two. -/
theorem quotient_all_squares_one (W : Subgroup G) [W.Normal]
    (hsquare : ∀ g : G, g ^ 2 ∈ W) : ∀ x : G ⧸ W, x ^ 2 = 1 := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W x
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (hsquare g)

/-- The quotient commutative group structure derived from all squares. -/
abbrev squareQuotientCommGroup (W : Subgroup G) [W.Normal]
    (hsquare : ∀ g : G, g ^ 2 ∈ W) : CommGroup (G ⧸ W) :=
  { (inferInstance : Group (G ⧸ W)) with
    mul_comm := mul_comm_of_all_squares_one (quotient_all_squares_one W hsquare) }

/-- The binary vector-space structure derived from the quotient's exponent. -/
abbrev squareQuotientModule (W : Subgroup G) [W.Normal]
    (hsquare : ∀ g : G, g ^ 2 ∈ W) :
    letI := squareQuotientCommGroup W hsquare
    Module (ZMod 2) (Additive (G ⧸ W)) := by
  letI := squareQuotientCommGroup W hsquare
  apply AddCommGroup.zmodModule
  intro x
  rw [two_nsmul]
  change x.toMul * x.toMul = 1
  simpa only [pow_two] using quotient_all_squares_one W hsquare x.toMul

/-- The actual quotient, written additively and indexed by the square
proof so its derived binary structure is inferred without extra assumptions. -/
def SquareQuotientSpace (W : Subgroup G) [W.Normal]
    (_hsquare : ∀ g : G, g ^ 2 ∈ W) := Additive (G ⧸ W)

instance squareQuotientSpaceAddCommGroup (W : Subgroup G) [W.Normal]
    (hsquare : ∀ g : G, g ^ 2 ∈ W) : AddCommGroup (SquareQuotientSpace W hsquare) := by
  letI := squareQuotientCommGroup W hsquare
  exact inferInstanceAs (AddCommGroup (Additive (G ⧸ W)))

instance squareQuotientSpaceModule (W : Subgroup G) [W.Normal]
    (hsquare : ∀ g : G, g ^ 2 ∈ W) : Module (ZMod 2) (SquareQuotientSpace W hsquare) := by
  apply AddCommGroup.zmodModule
  intro x
  rw [two_nsmul]
  change Additive.toMul x * Additive.toMul x = 1
  simpa only [pow_two] using quotient_all_squares_one W hsquare (Additive.toMul x)

section BinaryQuotient

variable (W : Subgroup G) [W.Normal] (hsquare : ∀ g : G, g ^ 2 ∈ W)

/-- The quotient's actual subgroups are precisely its binary subspaces. -/
def squareQuotientSubspaceOrderIso :
    Subgroup (G ⧸ W) ≃o Submodule (ZMod 2) (SquareQuotientSpace W hsquare) :=
  { toFun := fun H => AddSubgroup.toZModSubmodule 2 {
      carrier := {x | Additive.toMul x ∈ H}
      zero_mem' := H.one_mem
      add_mem' := H.mul_mem
      neg_mem' := H.inv_mem }
    invFun := fun L => {
      carrier := {x | Additive.ofMul x ∈ L}
      one_mem' := L.zero_mem
      mul_mem' := L.add_mem
      inv_mem' := L.neg_mem }
    left_inv := fun H => by ext; rfl
    right_inv := fun L => by ext; rfl
    map_rel_iff' := by intro H L; rfl }

/-- The image of the original kernel in the binary quotient by `W`. -/
def squareKernelSubmodule (π : G →* Q) : Submodule (ZMod 2) (SquareQuotientSpace W hsquare) :=
  squareQuotientSubspaceOrderIso W hsquare (π.ker.map (QuotientGroup.mk' W))

/-- Exact group-to-linear lift equivalence. No complement count is assumed. -/
def squareLiftComplementEquiv (π : G →* Q) (hπ : Function.Surjective π)
    (hW : W ≤ π.ker) :
    SquareLiftFibre π W ≃
      {L : Submodule (ZMod 2) (SquareQuotientSpace W hsquare) //
        IsCompl (squareKernelSubmodule W hsquare π) L} :=
  (quotientLiftComplementEquiv π hπ W hW).trans
    ((squareQuotientSubspaceOrderIso W hsquare).toEquiv.subtypeEquiv (fun _L =>
      (squareQuotientSubspaceOrderIso W hsquare).isCompl_iff))

include hsquare in
/-- Linear complements supply actual subgroup lifts whenever all squares
vanish in the quotient. -/
theorem lift_exists_of_squares (π : G →* Q) (hπ : Function.Surjective π)
    (hW : W ≤ π.ker) : Nonempty (SquareLiftFibre π W) := by
  obtain ⟨L, hL⟩ := (squareKernelSubmodule W hsquare π).exists_isCompl
  exact ⟨(squareLiftComplementEquiv W hsquare π hπ hW).symm ⟨L, hL⟩⟩

/-- Finiteness comes from the actual group quotient, not from an assumed
finite-dimensional model. -/
instance squareQuotientSpaceFinite [Finite G] : Finite (SquareQuotientSpace W hsquare) :=
  inferInstanceAs (Finite (Additive (G ⧸ W)))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The original quotient homomorphism, descended through `W` and regarded
as a binary linear map. -/
def squareQuotientLinearMap (π : G →* Multiplicative V) (hW : W ≤ π.ker) :
    SquareQuotientSpace W hsquare →ₗ[ZMod 2] V :=
  (QuotientGroup.lift W π hW).toAdditiveLeft.toZModLinearMap 2

@[simp] theorem squareQuotientLinearMap_mk (π : G →* Multiplicative V)
    (hW : W ≤ π.ker) (g : G) :
    squareQuotientLinearMap W hsquare π hW
      (Additive.ofMul (QuotientGroup.mk' W g)) = (π g).toAdd := rfl

theorem squareQuotientLinearMap_surjective (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (hW : W ≤ π.ker) :
    Function.Surjective (squareQuotientLinearMap W hsquare π hW) := by
  intro v
  obtain ⟨g, hg⟩ := hπ (Multiplicative.ofAdd v)
  refine ⟨Additive.ofMul (QuotientGroup.mk' W g), ?_⟩
  simpa only [squareQuotientLinearMap_mk] using congrArg Multiplicative.toAdd hg

/-- Its kernel is exactly the image of the original group kernel. -/
theorem squareQuotientLinearMap_ker (π : G →* Multiplicative V)
    (hW : W ≤ π.ker) :
    (squareQuotientLinearMap W hsquare π hW).ker = squareKernelSubmodule W hsquare π := by
  ext x
  change (QuotientGroup.lift W π hW) (Additive.toMul x) = 1 ↔
    Additive.toMul x ∈ π.ker.map (QuotientGroup.mk' W)
  rw [← QuotientGroup.ker_lift W π hW]
  rfl

/-- The vector-space quotient by the kernel image is the original binary
quotient, with an actual linear equivalence. -/
def squareQuotientQuotientEquiv (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (hW : W ≤ π.ker) :
    (SquareQuotientSpace W hsquare ⧸ squareKernelSubmodule W hsquare π) ≃ₗ[ZMod 2] V :=
  (Submodule.quotEquivOfEq _ _ (squareQuotientLinearMap_ker W hsquare π hW).symm).trans
    ((squareQuotientLinearMap W hsquare π hW).quotKerEquivOfSurjective
      (squareQuotientLinearMap_surjective W hsquare π hπ hW))

/-- Exact cardinality of the actual fixed-intersection lift fibre. The
remaining kernel factor is the genuine image `ker(π)/W`, not an abstract
parameter. -/
theorem squareLiftFibre_card [Finite G] (π : G →* Multiplicative V)
    (hπ : Function.Surjective π) (hW : W ≤ π.ker) :
    Nat.card (SquareLiftFibre π W) =
      2 ^ (Module.finrank (ZMod 2) V *
        Module.finrank (ZMod 2) (squareKernelSubmodule W hsquare π)) := by
  rw [Nat.card_congr (squareLiftComplementEquiv W hsquare π hπ hW), binary_complement_count]
  rw [(squareQuotientQuotientEquiv W hsquare π hπ hW).finrank_eq]

end BinaryQuotient

/-- Exact existence criterion for the full-image fibre in a central binary
extension. This tests squares, including the squares of individual lifts. -/
theorem lift_exists_iff_squares (π : G →* Q) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center G)
    (hkernel : ∀ g ∈ π.ker, g ^ 2 = 1) (hquotient : ∀ q : Q, q ^ 2 = 1)
    (W : Subgroup G) (hW : W ≤ π.ker) :
    Nonempty (SquareLiftFibre π W) ↔ ∀ g : G, g ^ 2 ∈ W := by
  letI : W.Normal := normal_of_le_central_kernel π hcentral W hW
  constructor
  · rintro ⟨H, hH⟩
    exact squares_mem_of_lift π hcentral hkernel hquotient W H hH.1 hH.2
  · intro hsquare
    exact lift_exists_of_squares W hsquare π hπ hW

/-- The actual subgroup fibre over a specified image, not necessarily the
whole binary quotient. -/
def ImageSquareLiftFibre (π : G →* Q) (U : Subgroup Q) (W : Subgroup G) :=
  {H : Subgroup G // H.map π = U ∧ H ⊓ π.ker = W}

theorem kernel_le_preimage (π : G →* Q) (U : Subgroup Q) : π.ker ≤ U.comap π := by
  intro g hg
  change π g ∈ U
  rw [show π g = 1 from hg]
  exact U.one_mem

/-- Restriction over a specified image retains the entire original kernel. -/
theorem subgroupComap_kernel (π : G →* Q) (U : Subgroup Q) :
    (π.subgroupComap U).ker = π.ker.subgroupOf (U.comap π) := by
  ext g
  change (⟨π g.1, g.2⟩ : U) = 1 ↔ π g.1 = 1
  exact Subtype.ext_iff

/-- The restricted kernel is canonically the original kernel, so a chosen
binary kernel chart transports without changing any coordinates. -/
def restrictedKernelEquiv (π : G →* Q) (U : Subgroup Q) :
    (π.subgroupComap U).ker ≃* π.ker where
  toFun k := ⟨k.1.1, by
    have h := congrArg Subtype.val k.2
    exact h⟩
  invFun k := ⟨⟨k.1, kernel_le_preimage π U k.2⟩, by
    apply Subtype.ext
    exact k.2⟩
  left_inv k := rfl
  right_inv k := rfl
  map_mul' k l := rfl

private theorem subgroupComap_map_image (π : G →* Q) (U : Subgroup Q)
    (L : Subgroup (U.comap π)) :
    (L.map (U.comap π).subtype).map π = (L.map (π.subgroupComap U)).map U.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem subgroupComap_kernel_map (π : G →* Q) (U : Subgroup Q) :
    (π.subgroupComap U).ker.map (U.comap π).subtype = π.ker := by
  rw [subgroupComap_kernel]
  exact Subgroup.map_subgroupOf_eq_of_le (kernel_le_preimage π U)

/-- Restriction of the entire actual image fibre, with no chosen kernel
intersection. This is the reduction used before the disjoint fibre sum. -/
def imageLiftEquiv (π : G →* Q) (U : Subgroup Q) :
    {H : Subgroup G // H.map π = U} ≃
      {L : Subgroup (U.comap π) // L.map (π.subgroupComap U) = ⊤} where
  toFun H := ⟨H.1.subgroupOf (U.comap π), by
    have hH : H.1 ≤ U.comap π := Subgroup.map_le_iff_le_comap.mp H.2.le
    apply Subgroup.map_injective U.subtype_injective
    rw [← subgroupComap_map_image, Subgroup.map_subgroupOf_eq_of_le hH, H.2,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]⟩
  invFun L := ⟨L.1.map (U.comap π).subtype, by
    rw [subgroupComap_map_image, L.2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]⟩
  left_inv H := by
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_le_iff_le_comap.mp H.2.le)
  right_inv L := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (U.comap π).subtype_injective L.1

/-- Exact restriction equivalence between literal ambient subgroups over
`U` and full-image subgroups of its preimage. -/
def imageSquareLiftFibreEquiv (π : G →* Q) (U : Subgroup Q)
    (W : Subgroup G) (hW : W ≤ π.ker) :
    ImageSquareLiftFibre π U W ≃
      SquareLiftFibre (π.subgroupComap U) (W.subgroupOf (U.comap π)) where
  toFun H := ⟨H.1.subgroupOf (U.comap π), by
    have hH : H.1 ≤ U.comap π := Subgroup.map_le_iff_le_comap.mp H.2.1.le
    constructor
    · apply Subgroup.map_injective U.subtype_injective
      rw [← subgroupComap_map_image, Subgroup.map_subgroupOf_eq_of_le hH, H.2.1]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [subgroupComap_kernel]
      change H.1.comap (U.comap π).subtype ⊓ π.ker.comap (U.comap π).subtype =
        W.comap (U.comap π).subtype
      rw [← Subgroup.comap_inf, H.2.2]⟩
  invFun L := ⟨L.1.map (U.comap π).subtype, by
    constructor
    · rw [subgroupComap_map_image, L.2.1]
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [← subgroupComap_kernel_map π U, ← Subgroup.map_inf _ _ _
        (U.comap π).subtype_injective, L.2.2]
      exact Subgroup.map_subgroupOf_eq_of_le (hW.trans (kernel_le_preimage π U))⟩
  left_inv H := by
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_le_iff_le_comap.mp H.2.1.le)
  right_inv L := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (U.comap π).subtype_injective L.1

/-- The square test over a specified image in the original ambient group.
No commutator-only replacement is made. -/
theorem image_lift_exists_iff_squares (π : G →* Q) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ Subgroup.center G)
    (hkernel : ∀ g ∈ π.ker, g ^ 2 = 1) (hquotient : ∀ q : Q, q ^ 2 = 1)
    (U : Subgroup Q) (W : Subgroup G) (hW : W ≤ π.ker) :
    Nonempty (ImageSquareLiftFibre π U W) ↔ ∀ g : G, π g ∈ U → g ^ 2 ∈ W := by
  have hc : (π.subgroupComap U).ker ≤ Subgroup.center (U.comap π) := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral (by
      have h := congrArg Subtype.val hk
      exact h)) g.1
  have hk : ∀ k ∈ (π.subgroupComap U).ker, k ^ 2 = 1 := by
    intro k hk
    apply Subtype.ext
    exact hkernel k.1 (by exact congrArg Subtype.val hk)
  have hq : ∀ q : U, q ^ 2 = 1 := by
    intro q
    apply Subtype.ext
    exact hquotient q.1
  have hw : W.subgroupOf (U.comap π) ≤ (π.subgroupComap U).ker := by
    rw [subgroupComap_kernel]
    exact Subgroup.comap_mono hW
  rw [(imageSquareLiftFibreEquiv π U W hW).nonempty_congr,
    lift_exists_iff_squares (π.subgroupComap U)
      (π.subgroupComap_surjective_of_surjective U hπ) hc hk hq _ hw]
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h g
    exact h g.1 g.2

/-- A quotient whose kernel lies in the Frattini subgroup detects full
projection for every subgroup, including lifts that omit part of the kernel. -/
theorem map_eq_top_iff_of_kernel_le_frattini [IsCoatomic (Subgroup G)]
    (π : G →* Q) (hπ : Function.Surjective π) (hker : π.ker ≤ frattini G)
    (H : Subgroup G) : H.map π = ⊤ ↔ H = ⊤ := by
  constructor
  · intro h
    apply frattini_nongenerating
    apply top_unique
    rw [← (map_eq_top_iff_sup_kernel π hπ H).mp h]
    exact sup_le_sup_left hker H
  · rintro rfl
    exact Subgroup.map_top_of_surjective π hπ

/-- The full-factor implication under its exact Frattini-kernel hypothesis.
Concrete critical actions must establish that hypothesis separately. -/
theorem full_projection_iff_of_frattini_kernel {D R : Type*} [Group D] [Group R]
    [IsCoatomic (Subgroup D)] (p : G →* D) (q : D →* R)
    (hq : Function.Surjective q) (hker : q.ker ≤ frattini D) (H : Subgroup G) :
    H.map p = ⊤ ↔ H.map (q.comp p) = ⊤ := by
  rw [← Subgroup.map_map]
  exact (map_eq_top_iff_of_kernel_le_frattini q hq hker (H.map p)).symm


end SymmetricSubgroupAsymptotics
