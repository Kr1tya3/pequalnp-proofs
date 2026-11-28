import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55754

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [9, 12]⟩], output := 13 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55754

theorem PEqualNP.Outside.L_meta_55754 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (14896307 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55754.c1, PEqualNP.Outside.L_meta_55754.f1, by decide +kernel, by decide +kernel⟩
