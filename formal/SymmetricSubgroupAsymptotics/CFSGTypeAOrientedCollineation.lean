import SymmetricSubgroupAsymptotics.CFSGTypeARootIncidenceGraph
import SymmetricSubgroupAsymptotics.CFSGTypeARootActionFaithfulness
import SymmetricSubgroupAsymptotics.CFSGProjectiveIncidenceCollineation
import SymmetricSubgroupAsymptotics.CFSGSumSideStabilizer
import SymmetricSubgroupAsymptotics.CFSGColorOrientationIndex

/-! The actual orientation-preserving automorphisms of PSL inject into
the canonical projective collineation group. The complementary orientation
factor is at most two, obtained from the connected incidence graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeAOrientedCollineation
open Matrix Module CFSGTypeAProjectivePointRoots CFSGTypeARootIncidence
open CFSGProjectiveIncidence CFSGTypeARootGeometryAction CFSGTypeARootIncidenceGraph
open CFSGProjectiveIncidenceCollineation CFSGSumSideStabilizer
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

abbrev PointType := Points (F:=F) (n:=Fin n)
abbrev HyperplaneType := Hyperplanes (F:=F) (n:=Fin n)

def orientedAutomorphisms (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    Subgroup (MulAut (PSL (F:=F) (n:=Fin n))) :=
  sideStabilizer.comap (rootPermutationHom p hn)

def geometryRestriction (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    orientedAutomorphisms (F:=F) p hn→*
      sideStabilizer (P:=PointType (F:=F) (n:=n)) (H:=HyperplaneType (F:=F) (n:=n)) where
  toFun a := ⟨rootPermutationHom p hn a.val,a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

def pointPermutationHom (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    orientedAutomorphisms (F:=F) p hn→*Equiv.Perm (PointType (F:=F) (n:=n)) :=
  leftHom.comp (geometryRestriction p hn)

def hyperplanePermutationHom (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    orientedAutomorphisms (F:=F) p hn→*Equiv.Perm (HyperplaneType (F:=F) (n:=n)) :=
  rightHom.comp (geometryRestriction p hn)

theorem pointPermutation_spec (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : orientedAutomorphisms (F:=F) p hn) (q : PointType (F:=F) (n:=n)) :
    rootPermutationHom p hn a.val (Sum.inl q)=Sum.inl (pointPermutationHom p hn a q) :=
  leftImage_spec (geometryRestriction p hn a) q

theorem hyperplanePermutation_spec (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : orientedAutomorphisms (F:=F) p hn) (h : HyperplaneType (F:=F) (n:=n)) :
    rootPermutationHom p hn a.val (Sum.inr h)=Sum.inr (hyperplanePermutationHom p hn a h) :=
  rightImage_spec (geometryRestriction p hn a) h

theorem permutations_preserve_incidence (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    (a : orientedAutomorphisms (F:=F) p hn)
    (q : PointType (F:=F) (n:=n)) (h : HyperplaneType (F:=F) (n:=n)) :
    Incident (pointPermutationHom p hn a q) (hyperplanePermutationHom p hn a h)↔Incident q h := by
  have hh := rootPermutation_graph_iff p hn a.val (Sum.inl q) (Sum.inr h)
  rw [pointPermutation_spec,hyperplanePermutation_spec] at hh
  exact hh

def collineationHom (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n) :
    orientedAutomorphisms (F:=F) p hn→*
      CFSGProjectiveFrameCoordinates.collineationGroup (F:=F) (n:=Fin n) where
  toFun a := ⟨pointPermutationHom p hn a,
    point_permutation_mem_collineationGroup _ _ (permutations_preserve_incidence p hn a)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem collineationHom_injective (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    [IsSimpleGroup (PSL (F:=F) (n:=Fin n))] :
    Function.Injective (collineationHom (F:=F) p hn) := by
  intro a b he
  have hpoint : pointPermutationHom p hn a=pointPermutationHom p hn b := congrArg Subtype.val he
  have hhyper : hyperplanePermutationHom p hn a=hyperplanePermutationHom p hn b := by
    apply hyperplane_permutation_unique (pointPermutationHom p hn a) _ _
      (permutations_preserve_incidence p hn a)
    intro q h
    rw [hpoint]
    exact permutations_preserve_incidence p hn b q h
  apply Subtype.ext
  apply CFSGTypeARootActionFaithfulness.rootPermutationHom_injective p hn
  apply Equiv.ext
  intro x
  cases x with
  | inl q =>
    rw [pointPermutation_spec,pointPermutation_spec,hpoint]
  | inr h =>
    rw [hyperplanePermutation_spec,hyperplanePermutation_spec,hhyper]

theorem automorphism_card_le_two_mul_collineation (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 3≤n)
    [IsSimpleGroup (PSL (F:=F) (n:=Fin n))] :
    Nat.card (MulAut (PSL (F:=F) (n:=Fin n)))≤
      2*Nat.card (CFSGProjectiveFrameCoordinates.collineationGroup (F:=F) (n:=Fin n)) := by
  letI : MulAction (MulAut (PSL (F:=F) (n:=Fin n))) (Vertex (F:=F) (n:=Fin n)) :=
    MulAction.compHom _ (rootPermutationHom p hn)
  let c := CFSGIncidenceOrientation.sideColoring (Incident (F:=F) (n:=Fin n))
  have hact : ∀a : MulAut (PSL (F:=F) (n:=Fin n)),∀x y,
      (graph (F:=F) (n:=Fin n)).Adj x y→(graph (F:=F) (n:=Fin n)).Adj (a • x) (a • y) := by
    intro a x y h
    exact (rootPermutation_graph_iff p hn a x y).mpr h
  have hside (x : Vertex (F:=F) (n:=Fin n)) : c x=CFSGSumSideStabilizer.side x := by
    cases x <;> rfl
  have hs : orientedAutomorphisms (F:=F) p hn=
      CFSGColorOrientationIndex.colorStabilizer (G:=MulAut (PSL (F:=F) (n:=Fin n))) c := by
    ext a
    change (∀x,CFSGSumSideStabilizer.side (rootPermutationHom p hn a x)=
      CFSGSumSideStabilizer.side x) ↔ ∀x,c (rootPermutationHom p hn a x)=c x
    simp only [hside]
  have hc := CFSGColorOrientationIndex.card_le_two_mul_stabilizer (graph_connected (F:=F) hn) c hact
  rw [←hs] at hc
  exact hc.trans (Nat.mul_le_mul_left 2
    (Nat.card_le_card_of_injective _ (collineationHom_injective (F:=F) p hn)))

end SymmetricSubgroupAsymptotics.CFSGTypeAOrientedCollineation
