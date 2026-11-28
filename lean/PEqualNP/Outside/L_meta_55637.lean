import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55637

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [9, 14]⟩], output := 15 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55637

theorem PEqualNP.Outside.L_meta_55637 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375329 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55637.c1, PEqualNP.Outside.L_meta_55637.f1, by decide +kernel, by decide +kernel⟩
