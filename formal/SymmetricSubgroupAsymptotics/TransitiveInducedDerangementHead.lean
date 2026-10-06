import SymmetricSubgroupAsymptotics.InducedElementOrbitCount
import SymmetricSubgroupAsymptotics.TransitiveDerangement

/-!
# A derangement bound for induced two-space heads

If an original subgroup has index at least two, its coset action is finite,
transitive, and nontrivial.  A derangement in that literal action has no
singleton cyclic orbit, so it has at most half as many cyclic orbits as
there are cosets.  The original induced-element head theorem then shows
that every subrepresentation of an induced two-space has head dimension at
most the original index.  Fibre twists are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

/-- A fixed-point-free element has no singleton cyclic orbit, so twice its
literal cyclic-orbit count is at most the size of the acted-on set. -/
theorem cyclicOrbitCount_mul_two_le_of_fixedBy_eq_empty
    {G X : Type} [Group G] [Finite X] [MulAction G X]
    (g : G) (hfree : MulAction.fixedBy X g = ∅) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) X) * 2 ≤
      Nat.card X := by
  let O := MulAction.orbitRel.Quotient (Subgroup.zpowers g) X
  letI : Fintype O := Fintype.ofFinite O
  have hsize (o : O) : 2 ≤ Nat.card o.orbit := by
    obtain ⟨x, hx⟩ := o.nonempty_orbit
    let x0 : o.orbit := ⟨x, hx⟩
    letI : Nonempty o.orbit := ⟨x0⟩
    have hpos : 0 < Nat.card o.orbit := Nat.card_pos
    by_contra hnot
    have hone : Nat.card o.orbit = 1 := by omega
    letI : Subsingleton o.orbit := (Nat.card_eq_one_iff_unique.mp hone).1
    let x1 : o.orbit := ⟨g • x, by
      have hrel : MulAction.orbitRel (Subgroup.zpowers g) X (g • x) x := by
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        exact ⟨⟨g, Subgroup.mem_zpowers g⟩, rfl⟩
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr
        ((Quotient.sound hrel).trans
          (MulAction.orbitRel.Quotient.mem_orbit.mp hx))⟩
    have hfix : g • x = x := congrArg Subtype.val (Subsingleton.elim x1 x0)
    have hxfix : x ∈ MulAction.fixedBy X g := hfix
    rw [hfree] at hxfix
    exact hxfix
  calc
    Nat.card O * 2 = ∑ _o : O, 2 := by
      simp only [Nat.card_eq_fintype_card, Finset.sum_const,
        Finset.card_univ, Nat.nsmul_eq_mul]
    _ ≤ ∑ o : O, Nat.card o.orbit := by
      exact Finset.sum_le_sum (fun o _ ↦ hsize o)
    _ = Nat.card X := by
      rw [← Nat.card_sigma]
      exact Nat.card_congr
        (MulAction.selfEquivSigmaOrbits' (Subgroup.zpowers g) X).symm

/-- Every subrepresentation of an original induced two-space has head at
most the original subgroup index. -/
theorem inducedTwoSpace_subrepresentationHead_le_index
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (rho : Representation (ZMod p) H V)
    (hdim : Module.finrank (ZMod p) V = 2)
    (hindex : 2 ≤ H.index)
    (M : Subrepresentation (Representation.ind H.subtype rho)) :
    Module.finrank (ZMod p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) G (ZMod p))) ≤ H.index := by
  let X := G ⧸ H
  have hcard_ne_one : Nat.card X ≠ 1 := by
    change H.index ≠ 1
    omega
  have hnotSubsingleton : ¬ Subsingleton X := by
    intro hsub
    exact hcard_ne_one
      (Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩)
  letI : Nontrivial X :=
    not_subsingleton_iff_nontrivial.mp hnotSubsingleton
  obtain ⟨g, hg⟩ := exists_fixedBy_eq_empty_of_pretransitive G X
  have hhead := induced_subrepresentationCharacterHead_le_cyclicOrbitCount
    (p := p) H rho g M
  have hcycles := cyclicOrbitCount_mul_two_le_of_fixedBy_eq_empty g hg
  rw [(representationCharacterHeadEquiv M.toRepresentation).finrank_eq,
    hdim] at hhead
  exact hhead.trans (by simpa only [X] using hcycles)

/-- Restricting an original induced representation to a subgroup does not
invalidate the literal cyclic-orbit head bound.  The subrepresentation need
only be invariant under the subgroup; its head still embeds in the fixed
space of the original induced module at the selected subgroup element. -/
theorem inducedRestriction_subrepresentationHead_le_cyclicOrbitCount
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (H P : Subgroup G) (rho : Representation (ZMod p) H V)
    (g : P)
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype)) :
    Module.finrank (ZMod p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) P (ZMod p))) ≤
      Nat.card (MulAction.orbitRel.Quotient
          (Subgroup.zpowers (g : G)) (G ⧸ H)) *
        Module.finrank (ZMod p) V := by
  let D := DoubleCoset.Quotient
    (H : Set G) (Subgroup.zpowers (g : G) : Set G)
  letI : Finite D := Finite.of_surjective
    (DoubleCoset.mk H (Subgroup.zpowers (g : G)))
    (fun q ↦ ⟨q.out, DoubleCoset.out_eq' _ _ q⟩)
  letI : Fintype D := Fintype.ofFinite D
  have hhead := subrepresentationHead_le_ambient_elementFixedSpace
    ((Representation.ind H.subtype rho).comp P.subtype) M g
  have hfixed := induced_elementFixedSpace_le_orbitRepresentatives
    H rho (g : G) (fun q : D ↦ q.out)
      (cyclicOrbitRepresentativeCover_doubleCoset H (g : G))
  have hfixed' : Module.finrank (ZMod p)
      (representationElementFixedSpace
        ((Representation.ind H.subtype rho).comp P.subtype) g) ≤
      Nat.card D * Module.finrank (ZMod p) V := by
    change Module.finrank (ZMod p)
        (representationElementFixedSpace
          (Representation.ind H.subtype rho) (g : G)) ≤
      Nat.card D * Module.finrank (ZMod p) V
    simpa only [Nat.card_eq_fintype_card] using hfixed
  rw [Nat.card_congr
    (inducedDoubleCosetOrbitEquiv H (Subgroup.zpowers (g : G)))] at hfixed'
  exact hhead.trans (by simpa only [D] using hfixed')

/-- If the restricting subgroup is transitive on the original cosets, every
subrepresentation of an induced two-space has head at most the original
index.  This is the form used after pulling a scalar Schur-row kernel back
to the original block action. -/
theorem inducedTwoSpace_restricted_subrepresentationHead_le_index
    {p : ℕ} [Fact p.Prime]
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (H P : Subgroup G) (rho : Representation (ZMod p) H V)
    (hdim : Module.finrank (ZMod p) V = 2)
    [MulAction.IsPretransitive P (G ⧸ H)]
    (hindex : 2 ≤ H.index)
    (M : Subrepresentation
      ((Representation.ind H.subtype rho).comp P.subtype)) :
    Module.finrank (ZMod p)
        (M.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod p) P (ZMod p))) ≤ H.index := by
  let X := G ⧸ H
  have hcard_ne_one : Nat.card X ≠ 1 := by
    change H.index ≠ 1
    omega
  have hnotSubsingleton : ¬ Subsingleton X := by
    intro hsub
    exact hcard_ne_one
      (Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩)
  letI : Nontrivial X :=
    not_subsingleton_iff_nontrivial.mp hnotSubsingleton
  obtain ⟨g, hg⟩ := exists_fixedBy_eq_empty_of_pretransitive P X
  have hhead := inducedRestriction_subrepresentationHead_le_cyclicOrbitCount
    H P rho g M
  have hcycles := cyclicOrbitCount_mul_two_le_of_fixedBy_eq_empty
    (g : G) (by simpa only [X] using hg)
  have hhead' := hhead
  rw [hdim] at hhead'
  exact hhead'.trans (by simpa only [X] using hcycles)

end SymmetricSubgroupAsymptotics

end
