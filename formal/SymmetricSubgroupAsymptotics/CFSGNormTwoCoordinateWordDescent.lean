import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateInversionCount

/-! Finite inversion drops telescope along a literal word whose successive
simple images are negative. The hypothesis records the actual prefixes,
without a Coxeter presentation or enumeration of the Weyl group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDescent
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateInversionCount
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem inversionCount_append_of_prefix_negative (w v : List (Fin r))
    (hneg : ∀u i t,v=u++i::t→
      ∀j,(wordRoot A hs hp b₀ s₀ (w++u) (s₀ i)).val j≤0) :
    inversionCount A hd hs hp ho (w++v)+v.length=inversionCount A hd hs hp ho w := by
  induction v generalizing w with
  | nil=>simp only [List.append_nil,List.length_nil,add_zero]
  | cons i v ih=>
    have hfirst := inversionCount_append_simple A hd hs hp ho w i
      (by simpa only [List.append_nil] using hneg [] i v rfl)
    have hrest : ∀u j t,v=u++j::t→
        ∀k,(wordRoot A hs hp b₀ s₀ ((w++[i])++u) (s₀ j)).val k≤0 := by
      intro u j t he
      have hpref : i::v=(i::u)++j::t := by rw [he]; rfl
      simpa only [List.append_assoc,List.singleton_append] using hneg (i::u) j t hpref
    have htail := ih (w++[i]) hrest
    have he : (w++[i])++v=w++(i::v) := by
      simp only [List.append_assoc,List.singleton_append]
    rw [he] at htail
    simp only [List.length_cons]
    omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDescent
