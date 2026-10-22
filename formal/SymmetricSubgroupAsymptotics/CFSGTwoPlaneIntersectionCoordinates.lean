import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Algebra.Module.Submodule.Equiv
import Lean.Elab.Tactic.Omega

/-! A two-plane meeting disjoint P,Q in points is determined by those
SAME two intersections. Over a finite field, the number of such planes
is at most (q+1)^2 when P,Q themselves have dimension two. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionCoordinates
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem eq_join_intersections (P Q R : Submodule K V) (hPQ : Disjoint P Q)
    (hR : Module.finrank K R = 2)
    (hPR : Module.finrank K (P ⊓ R : Submodule K V) = 1)
    (hQR : Module.finrank K (Q ⊓ R : Submodule K V) = 1) : R = (P ⊓ R) ⊔ (Q ⊓ R) := by
  let X : Submodule K V := P ⊓ R
  let Y : Submodule K V := Q ⊓ R
  have hx : Module.finrank K X = 1 := hPR
  have hy : Module.finrank K Y = 1 := hQR
  have hd : Disjoint X Y := hPQ.mono inf_le_left inf_le_left
  have hm := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hd.eq_bot, finrank_bot, hx, hy, add_zero] at hm
  have hs : Module.finrank K (X ⊔ Y : Submodule K V) = 2 := by omega
  exact (Submodule.eq_of_le_of_finrank_le (sup_le inf_le_right inf_le_right) (by rw [hR, hs])).symm

abbrev PointInside (P : Submodule K V) := {L : Submodule K P // Module.finrank K L = 1}

abbrev Crossing (P Q : Submodule K V) := {R : Submodule K V //
  Module.finrank K R = 2 ∧ Module.finrank K (P ⊓ R : Submodule K V) = 1 ∧
    Module.finrank K (Q ⊓ R : Submodule K V) = 1}

def intersectionPoint (P R : Submodule K V)
    (hd : Module.finrank K (P ⊓ R : Submodule K V) = 1) : PointInside P := by
  refine ⟨R.comap P.subtype, ?_⟩
  have he : (R.comap P.subtype).map P.subtype = P ⊓ R := Submodule.map_comap_subtype P R
  have hm := congrArg (fun T : Submodule K V => Module.finrank K T) he
  have hf := Submodule.finrank_map_subtype_eq P (R.comap P.subtype)
  exact hf.symm.trans (hm.trans hd)

def coordinates (P Q : Submodule K V) (R : Crossing P Q) : PointInside P × PointInside Q :=
  (intersectionPoint P R.val R.property.2.1, intersectionPoint Q R.val R.property.2.2)

theorem coordinates_injective (P Q : Submodule K V) (hPQ : Disjoint P Q) :
    Function.Injective (coordinates P Q) := by
  intro R S he
  have hP : R.val.comap P.subtype = S.val.comap P.subtype :=
    congrArg (fun z : PointInside P × PointInside Q => z.1.val) he
  have hQ : R.val.comap Q.subtype = S.val.comap Q.subtype :=
    congrArg (fun z : PointInside P × PointInside Q => z.2.val) he
  have hp := congrArg (fun L : Submodule K P => L.map P.subtype) hP
  have hq := congrArg (fun L : Submodule K Q => L.map Q.subtype) hQ
  dsimp only at hp hq
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype] at hp hq
  apply Subtype.ext
  calc
    R.val = (P ⊓ R.val) ⊔ (Q ⊓ R.val) :=
      eq_join_intersections P Q R.val hPQ R.property.1 R.property.2.1 R.property.2.2
    _ = (P ⊓ S.val) ⊔ (Q ⊓ S.val) := by rw [hp, hq]
    _ = S.val := (eq_join_intersections P Q S.val hPQ S.property.1 S.property.2.1 S.property.2.2).symm

omit [FiniteDimensional K V] in
theorem pointInside_card [Finite K] (P : Submodule K V) (hP : Module.finrank K P = 2) :
    Nat.card (PointInside P) = Nat.card K + 1 := by
  exact (Nat.card_congr (Projectivization.equivSubmodule K P).symm).trans
    (Projectivization.card_of_finrank_two K P hP)

theorem crossing_finite [Finite K] [Finite V] (P Q : Submodule K V) (hPQ : Disjoint P Q) :
    Finite (Crossing P Q) := by
  letI : Finite (PointInside P) := Finite.of_equiv (ℙ K P) (Projectivization.equivSubmodule K P)
  letI : Finite (PointInside Q) := Finite.of_equiv (ℙ K Q) (Projectivization.equivSubmodule K Q)
  exact Finite.of_injective (coordinates P Q) (coordinates_injective P Q hPQ)

theorem crossing_card_le [Finite K] [Finite V] (P Q : Submodule K V)
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2) (hPQ : Disjoint P Q) :
    Nat.card (Crossing P Q) ≤ (Nat.card K + 1) ^ 2 := by
  letI : Finite (PointInside P) := Finite.of_equiv (ℙ K P) (Projectivization.equivSubmodule K P)
  letI : Finite (PointInside Q) := Finite.of_equiv (ℙ K Q) (Projectivization.equivSubmodule K Q)
  have hb := Nat.card_le_card_of_injective (coordinates P Q) (coordinates_injective P Q hPQ)
  rw [Nat.card_prod, pointInside_card P hP, pointInside_card Q hQ] at hb
  simpa only [pow_two] using hb

end SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionCoordinates
