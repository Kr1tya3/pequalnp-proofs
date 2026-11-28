import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55008

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [7, 12]⟩], output := 13 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55008

theorem PEqualNP.Outside.L_meta_55008 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147362 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55008.c1, PEqualNP.Outside.L_meta_55008.f1, by decide +kernel, by decide +kernel⟩
