import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55006

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [8, 14]⟩], output := 15 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55006

theorem PEqualNP.Outside.L_meta_55006 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147347 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55006.c1, PEqualNP.Outside.L_meta_55006.f1, by decide +kernel, by decide +kernel⟩
