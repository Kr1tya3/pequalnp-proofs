import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1346

open PEqualNP.CircuitLowerBounds
open Classical

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

def val (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false

lemma eval_eq_val (gs : List Gate) (n o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = val gs n x o := rfl

lemma val_input (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gs n x w = x ⟨w, hw⟩ := wires_input ⟨gs, 0⟩ x w hw

lemma val_gate (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    val gs n x (n + j) = g.op.eval (g.inputs.map fun a => if a < n + j then val gs n x a else false) :=
  wires_gate_ofFn ⟨gs, 0⟩ x j g hg

def Fv (gs : List Gate) (n w : ℕ) : (Fin n → Bool) → Bool := fun x => val gs n x w

def eff (gs : List Gate) (n j a : ℕ) : (Fin n → Bool) → Bool :=
  fun x => if a < n + j then val gs n x a else false

def Nonconst {n : ℕ} (φ : (Fin n → Bool) → Bool) : Prop := ∃ x y, φ x ≠ φ y

def IsRep (gs : List Gate) (n j : ℕ) : Prop :=
  j < gs.length ∧ Nonconst (Fv gs n (n + j)) ∧ (∀ v : Fin n, Fv gs n (n + j) ≠ fun x => x v) ∧
    ∀ i < j, Fv gs n (n + i) ≠ Fv gs n (n + j)

noncomputable def repF (gs : List Gate) (n : ℕ) (φ : (Fin n → Bool) → Bool) : ℕ :=
  if h : ∃ v : Fin n, φ = fun x => x v then (Classical.choose h).val
  else if h2 : ∃ i, i < gs.length ∧ Fv gs n (n + i) = φ then n + Nat.find h2 else 0

lemma val_oob (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : n + gs.length ≤ w) :
    val gs n x w = false := wires_oob ⟨gs, 0⟩ x w hw

lemma Fv_input (gs : List Gate) (n w : ℕ) (hw : w < n) : Fv gs n w = fun x => x ⟨w, hw⟩ := by
  funext x
  exact val_input gs n x w hw

lemma repF_var (gs : List Gate) (n : ℕ) (φ : (Fin n → Bool) → Bool)
    (h : ∃ v : Fin n, φ = fun x => x v) :
    repF gs n φ < n ∧ Fv gs n (repF gs n φ) = φ := by
  have e : repF gs n φ = (Classical.choose h).val := by rw [repF, dif_pos h]
  have hv := Classical.choose_spec h
  rw [e]
  refine ⟨(Classical.choose h).isLt, ?_⟩
  rw [Fv_input gs n _ (Classical.choose h).isLt]
  conv_rhs => rw [hv]

lemma repF_gate (gs : List Gate) (n : ℕ) (φ : (Fin n → Bool) → Bool)
    (hv : ¬ ∃ v : Fin n, φ = fun x => x v) (i0 : ℕ) (hi0 : i0 < gs.length)
    (hf : Fv gs n (n + i0) = φ) :
    ∃ i, repF gs n φ = n + i ∧ i ≤ i0 ∧ i < gs.length ∧ Fv gs n (n + i) = φ ∧
      ∀ i' < i, Fv gs n (n + i') ≠ φ := by
  have h2 : ∃ i, i < gs.length ∧ Fv gs n (n + i) = φ := ⟨i0, hi0, hf⟩
  refine ⟨Nat.find h2, by rw [repF, dif_neg hv, dif_pos h2], Nat.find_min' h2 ⟨hi0, hf⟩,
    (Nat.find_spec h2).1, (Nat.find_spec h2).2, fun i' hi' h' => ?_⟩
  have := (Nat.find_spec h2).1
  exact Nat.find_min h2 hi' ⟨by omega, h'⟩

lemma eff_rep (gs : List Gate) (n j a : ℕ) (hφ : Nonconst (eff gs n j a)) :
    Fv gs n (repF gs n (eff gs n j a)) = eff gs n j a ∧
    (repF gs n (eff gs n j a) < n ∨
      ∃ i, repF gs n (eff gs n j a) = n + i ∧ i < j ∧ IsRep gs n i) := by
  have ha : a < n + j := by
    by_contra h
    obtain ⟨x, y, hxy⟩ := hφ
    simp [eff, h] at hxy
  have he : eff gs n j a = Fv gs n a := by
    funext x
    simp [eff, Fv, ha]
  by_cases hv : ∃ v : Fin n, eff gs n j a = fun x => x v
  · exact ⟨(repF_var gs n _ hv).2, Or.inl (repF_var gs n _ hv).1⟩
  · have han : n ≤ a := by
      by_contra h
      push_neg at h
      exact hv ⟨⟨a, h⟩, by rw [he, Fv_input gs n a h]⟩
    have hlt : a - n < gs.length := by
      by_contra hge
      obtain ⟨x, y, hxy⟩ := hφ
      apply hxy
      rw [he]
      simp only [Fv]
      rw [val_oob gs n x a (by omega), val_oob gs n y a (by omega)]
    obtain ⟨i, hi, hile, hiL, hFi, hmin⟩ := repF_gate gs n _ hv (a - n) hlt
      (by rw [he, show n + (a - n) = a by omega])
    refine ⟨by rw [hi]; exact hFi, Or.inr ⟨i, hi, by omega, hiL, by rw [hFi]; exact hφ,
      fun v hv' => hv ⟨v, by rw [← hFi]; exact hv'⟩, fun i' hi' h' => hmin i' hi' (h'.trans hFi)⟩⟩

lemma rep_not_const (gs : List Gate) (n j : ℕ) (hr : IsRep gs n j) (c : Bool)
    (h : ∀ x, Fv gs n (n + j) x = c) : False := by
  obtain ⟨x, y, hxy⟩ := hr.2.1
  exact hxy (by rw [h x, h y])

lemma rep_not_copy (gs : List Gate) (n j a : ℕ) (hr : IsRep gs n j)
    (h : ∀ x, Fv gs n (n + j) x = eff gs n j a x) : False := by
  by_cases hc : Nonconst (eff gs n j a)
  · obtain ⟨hF, hr'⟩ := eff_rep gs n j a hc
    rcases hr' with hlt | ⟨i, hi, hij, -⟩
    · apply hr.2.2.1 ⟨_, hlt⟩
      funext x
      rw [h x, ← congrFun hF x]
      exact val_input gs n x _ hlt
    · apply hr.2.2.2 i hij
      funext x
      rw [h x, ← hF, hi]
  · apply rep_not_const gs n j hr (eff gs n j a (fun _ => false))
    intro x
    rw [h x]
    by_contra hne
    exact hc ⟨x, _, hne⟩

lemma Fv_gate (gs : List Gate) (n j : ℕ) (g : Gate) (hg : gs[j]? = some g) (x : Fin n → Bool) :
    Fv gs n (n + j) x = g.op.eval (g.inputs.map fun a => eff gs n j a x) :=
  val_gate gs n x j g hg

lemma const_of (n : ℕ) (φ : (Fin n → Bool) → Bool) (h : ¬ Nonconst φ) :
    ∀ x, φ x = φ (fun _ => false) := by
  intro x
  by_contra hne
  exact h ⟨x, _, hne⟩

lemma rep_ao (gs : List Gate) (n j : ℕ) (g : Gate) (hg : gs[j]? = some g) (hr : IsRep gs n j)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    ∃ a b, g.inputs = [a, b] ∧ Nonconst (eff gs n j a) ∧ Nonconst (eff gs n j b) ∧
      eff gs n j a ≠ eff gs n j b := by
  have hF := Fv_gate gs n j g hg
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exfalso
    rcases hop with h | h
    · exact rep_not_const gs n j hr true (fun x => by rw [hF x, hin, h]; rfl)
    · exact rep_not_const gs n j hr false (fun x => by rw [hF x, hin, h]; rfl)
  · exfalso
    apply rep_not_copy gs n j a hr
    intro x
    rw [hF x, hin]
    rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
  · have key : ∀ u v : ℕ, (u = a ∧ v = b) ∨ (u = b ∧ v = a) → ¬ Nonconst (eff gs n j u) → False := by
      intro u v huv hu
      have hc := const_of n _ hu
      have hF2 : ∀ x, Fv gs n (n + j) x = g.op.eval [eff gs n j u (fun _ => false), eff gs n j v x] := by
        intro x
        rw [hF x, hin]
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [List.map_cons, List.map_nil, hc x]
        · simp only [List.map_cons, List.map_nil, hc x]
          rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
      cases hcu : eff gs n j u (fun _ => false) <;> rcases hop with h | h
      · exact rep_not_const gs n j hr false (fun x => by rw [hF2 x, hcu, h]; simp [GateOp.eval])
      · exact rep_not_copy gs n j v hr (fun x => by rw [hF2 x, hcu, h]; simp [GateOp.eval])
      · exact rep_not_copy gs n j v hr (fun x => by rw [hF2 x, hcu, h]; simp [GateOp.eval])
      · exact rep_not_const gs n j hr true (fun x => by rw [hF2 x, hcu, h]; simp [GateOp.eval])
    refine ⟨a, b, rfl, ?_, ?_, fun hab => ?_⟩
    · by_contra h'; exact key a b (Or.inl ⟨rfl, rfl⟩) h'
    · by_contra h'; exact key b a (Or.inr ⟨rfl, rfl⟩) h'
    · apply rep_not_copy gs n j a hr
      intro x
      rw [hF x, hin]
      simp only [List.map_cons, List.map_nil, ← hab]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
  · exfalso
    rw [hin] at hlen
    simp at hlen

lemma rep_not (gs : List Gate) (n j : ℕ) (g : Gate) (hg : gs[j]? = some g) (hr : IsRep gs n j)
    (hop : g.op = GateOp.not) :
    ∃ a rest, g.inputs = a :: rest ∧ Nonconst (eff gs n j a) := by
  have hF := Fv_gate gs n j g hg
  rcases hin : g.inputs with _ | ⟨a, rest⟩
  · exfalso
    exact rep_not_const gs n j hr true (fun x => by rw [hF x, hin, hop]; rfl)
  · refine ⟨a, rest, rfl, ?_⟩
    by_contra h'
    have hc := const_of n _ h'
    apply rep_not_const gs n j hr (!(eff gs n j a (fun _ => false)))
    intro x
    rw [hF x, hin, hop]
    simp [GateOp.eval, hc x]

def rel (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def Reads (gs : List Gate) (n k i : ℕ) : Prop :=
  ∃ g, gs[k]? = some g ∧ ∃ a ∈ rel g, repF gs n (eff gs n k a) = n + i

def need (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) : Prop :=
  IsRep gs n i ∧ ((∃ o : Fin m, Fv gs n (out o) = Fv gs n (n + i)) ∨
    ∃ k, ∃ (_ : i < k) (_ : k < gs.length), need gs n m out k ∧ Reads gs n k i)
termination_by gs.length - i
decreasing_by omega

lemma need_unfold (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) :
    need gs n m out i ↔ IsRep gs n i ∧ ((∃ o : Fin m, Fv gs n (out o) = Fv gs n (n + i)) ∨
      ∃ k, ∃ (_ : i < k) (_ : k < gs.length), need gs n m out k ∧ Reads gs n k i) := by
  rw [need]

noncomputable def T (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) : Finset ℕ :=
  (Finset.range gs.length).filter (fun i => need gs n m out i)

lemma mem_T (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) :
    i ∈ T gs n m out ↔ i < gs.length ∧ need gs n m out i := by
  simp [T]

noncomputable def iso (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) :
    Fin (T gs n m out).card ≃o {x // x ∈ T gs n m out} :=
  (T gs n m out).orderIsoOfFin rfl

noncomputable def pos (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i ∈ T gs n m out then ((iso gs n m out).symm ⟨i, h⟩).val else 0

noncomputable def sig (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (a : ℕ) : ℕ :=
  if a < n then a else n + pos gs n m out (a - n)

lemma sig_lt (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (a : ℕ) (h : a < n) :
    sig gs n m out a = a := by
  simp [sig, h]

lemma sig_gate (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) :
    sig gs n m out (n + i) = n + pos gs n m out i := by
  simp [sig]

noncomputable def newGate (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (j : ℕ) : Gate :=
  match gs[j]? with
  | some g => ⟨g.op, g.inputs.map fun a => sig gs n m out (repF gs n (eff gs n j a))⟩
  | none => ⟨GateOp.and, []⟩

lemma newGate_some (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    newGate gs n m out j = ⟨g.op, g.inputs.map fun a => sig gs n m out (repF gs n (eff gs n j a))⟩ := by
  simp [newGate, hg]

noncomputable def gl (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) : List Gate :=
  List.ofFn fun p : Fin (T gs n m out).card => newGate gs n m out ((iso gs n m out) p).val

lemma gl_length (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) :
    (gl gs n m out).length = (T gs n m out).card := by
  simp [gl]

lemma gl_getElem? (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (p : Fin (T gs n m out).card) :
    (gl gs n m out)[p.val]? = some (newGate gs n m out ((iso gs n m out) p).val) := by
  simp [gl]

lemma pos_lt (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) (hi : i ∈ T gs n m out) :
    pos gs n m out i < (T gs n m out).card := by
  simp only [pos, hi, ↓reduceDIte]
  exact Fin.isLt _

lemma iso_pos (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i : ℕ) (hi : i ∈ T gs n m out) :
    ((iso gs n m out) ⟨pos gs n m out i, pos_lt gs n m out i hi⟩).val = i := by
  simp only [pos, hi, ↓reduceDIte, Fin.eta, OrderIso.apply_symm_apply]

lemma pos_iso (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (p : Fin (T gs n m out).card) :
    pos gs n m out ((iso gs n m out) p).val = p.val := by
  simp only [pos, ((iso gs n m out) p).prop, ↓reduceDIte, Subtype.coe_eta, OrderIso.symm_apply_apply]

lemma pos_strict (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (i j : ℕ)
    (hi : i ∈ T gs n m out) (hj : j ∈ T gs n m out) (hij : i < j) :
    pos gs n m out i < pos gs n m out j := by
  simp only [pos, hi, hj, ↓reduceDIte]
  have : ((⟨i, hi⟩ : {x // x ∈ T gs n m out}) < ⟨j, hj⟩) := hij
  exact (iso gs n m out).symm.lt_iff_lt.mpr this

lemma rel_ao (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) : rel g = g.inputs := by
  rcases hop with h | h <;> simp [rel, h]

lemma rel_not (g : Gate) (hop : g.op = GateOp.not) : rel g = g.inputs.take 1 := by
  simp [rel, hop]

lemma gl_val (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∀ j, j ∈ T gs n m out → val (gl gs n m out) n x (n + pos gs n m out j) = Fv gs n (n + j) x := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  obtain ⟨hjL, hneed⟩ := (mem_T gs n m out j).mp hj
  have hr : IsRep gs n j := ((need_unfold gs n m out j).mp hneed).1
  obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem hjL⟩
  have hgl : (gl gs n m out)[pos gs n m out j]? = some (newGate gs n m out j) := by
    have := gl_getElem? gs n m out ⟨pos gs n m out j, pos_lt gs n m out j hj⟩
    rwa [iso_pos gs n m out j hj] at this
  rw [val_gate _ n x _ _ hgl, newGate_some gs n m out j g hg, Fv_gate gs n j g hg x]
  simp only [List.map_map]
  have good : ∀ a ∈ rel g, Nonconst (eff gs n j a) →
      (if sig gs n m out (repF gs n (eff gs n j a)) < n + pos gs n m out j then
        val (gl gs n m out) n x (sig gs n m out (repF gs n (eff gs n j a))) else false) =
        eff gs n j a x := by
    intro a ha hc
    obtain ⟨hF, hcase⟩ := eff_rep gs n j a hc
    rcases hcase with hlt | ⟨i, hi, hij, hri⟩
    · rw [sig_lt gs n m out _ hlt, if_pos (by omega), val_input _ n x _ hlt, ← congrFun hF x]
      exact (val_input gs n x _ hlt).symm
    · have hiT : i ∈ T gs n m out := (mem_T gs n m out i).mpr ⟨hri.1,
        (need_unfold gs n m out i).mpr ⟨hri, Or.inr ⟨j, hij, hjL, hneed, g, hg, a, ha, hi⟩⟩⟩
      have hp := pos_strict gs n m out i j hiT hj hij
      rw [← congrFun hF x, hi, sig_gate, if_pos (by omega), ih i hij hiT]
  have hgm := hgs g (List.mem_of_getElem? hg)
  rcases hgm.1 with hop | hop | hop
  · obtain ⟨a, b, hin, ha, hb, -⟩ := rep_ao gs n j g hg hr (Or.inl hop) hgm.2
    have hrel := rel_ao g (Or.inl hop)
    rw [hin]
    simp only [List.map_cons, List.map_nil, Function.comp_apply]
    rw [good a (by rw [hrel, hin]; simp) ha, good b (by rw [hrel, hin]; simp) hb]
  · obtain ⟨a, b, hin, ha, hb, -⟩ := rep_ao gs n j g hg hr (Or.inr hop) hgm.2
    have hrel := rel_ao g (Or.inr hop)
    rw [hin]
    simp only [List.map_cons, List.map_nil, Function.comp_apply]
    rw [good a (by rw [hrel, hin]; simp) ha, good b (by rw [hrel, hin]; simp) hb]
  · obtain ⟨a, rest, hin, ha⟩ := rep_not gs n j g hg hr hop
    have hrel := rel_not g hop
    rw [hin, hop]
    simp only [List.map_cons, Function.comp_apply, GateOp.eval, List.headD_cons]
    rw [good a (by rw [hrel, hin]; simp) ha]

lemma sig_val (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (r : ℕ) (hr : r < n ∨ ∃ i, r = n + i ∧ i ∈ T gs n m out) (x : Fin n → Bool) :
    val (gl gs n m out) n x (sig gs n m out r) = Fv gs n r x := by
  rcases hr with hlt | ⟨i, rfl, hi⟩
  · rw [sig_lt gs n m out r hlt, val_input _ n x r hlt]
    exact (val_input gs n x r hlt).symm
  · rw [sig_gate]
    exact gl_val gs n m out hgs x i hi

lemma read_val (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j ∈ T gs n m out) (g : Gate) (hg : gs[j]? = some g) (a : ℕ) (ha : a ∈ rel g)
    (hc : Nonconst (eff gs n j a)) (x : Fin n → Bool) :
    val (gl gs n m out) n x (sig gs n m out (repF gs n (eff gs n j a))) = eff gs n j a x := by
  obtain ⟨hjL, hneed⟩ := (mem_T gs n m out j).mp hj
  obtain ⟨hF, hcase⟩ := eff_rep gs n j a hc
  rw [sig_val gs n m out hgs _ ?_ x, hF]
  rcases hcase with hlt | ⟨i, hi, hij, hri⟩
  · exact Or.inl hlt
  · exact Or.inr ⟨i, hi, (mem_T gs n m out i).mpr ⟨hri.1,
      (need_unfold gs n m out i).mpr ⟨hri, Or.inr ⟨j, hij, hjL, hneed, g, hg, a, ha, hi⟩⟩⟩⟩

lemma gl_spec (gs : List Gate) (n m : ℕ) (out : Fin m → ℕ) (q : ℕ) (hq : q < (gl gs n m out).length) :
    ∃ j g, j ∈ T gs n m out ∧ pos gs n m out j = q ∧ gs[j]? = some g ∧
      (gl gs n m out)[q] = ⟨g.op, g.inputs.map fun a => sig gs n m out (repF gs n (eff gs n j a))⟩ := by
  have hq' : q < (T gs n m out).card := by rwa [gl_length] at hq
  set p : Fin (T gs n m out).card := ⟨q, hq'⟩
  have hjT := ((iso gs n m out) p).prop
  have hjL := ((mem_T gs n m out _).mp hjT).1
  refine ⟨((iso gs n m out) p).val, _, hjT, pos_iso gs n m out p,
    List.getElem?_eq_getElem hjL, ?_⟩
  have h1 := gl_getElem? gs n m out p
  rw [newGate_some gs n m out _ _ (List.getElem?_eq_getElem hjL)] at h1
  rw [List.getElem?_eq_getElem hq] at h1
  exact Option.some.inj h1

lemma rep_self (gs : List Gate) (n j : ℕ) (hr : IsRep gs n j) :
    repF gs n (Fv gs n (n + j)) = n + j := by
  obtain ⟨i, hi, hij, -, hFi, -⟩ := repF_gate gs n _ (fun ⟨v, hv⟩ => hr.2.2.1 v hv) j hr.1 rfl
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact absurd hFi (hr.2.2.2 i h)
  · rw [hi, h]

lemma main (n m : ℕ) (S : Fin m → Finset (Fin n)) (hS : ∀ ic : Fin m, 2 ≤ (S ic).card)
    (gates : List Gate) (out : Fin m → ℕ)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hout : ∀ (o : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (ι : Fin 1 → Fin gates.length)
    (hι : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → ∃ r : Fin 1, ι r = q)
    (I : Finset (Fin gates.length))
    (hI : ∀ q2 : Fin gates.length, ((gates.get q2).op = GateOp.and ∨ (gates.get q2).op = GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) :
    (∃ c : GateOp, (c = GateOp.and ∨ c = GateOp.or) ∧ ∀ (o1 : Fin m) (x1 : Fin n → Bool), Circuit.eval ⟨gates.set (ι 0).val ⟨c, []⟩, out o1⟩ (List.ofFn x1) = Circuit.eval ⟨gates, out o1⟩ (List.ofFn x1)) ∨ ∃ (gl : List Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = GateOp.and ∨ (gl.get q4).op = GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = GateOp.and ∨ (gl.get kr).op = GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = GateOp.and ∨ (gl.get jr4).op = GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · left
    exact ⟨GateOp.and, Or.inl rfl, fun o1 => absurd o1.isLt (by omega)⟩
  right
  have hφ : ∀ o x, Fv gates n (out o) x = decide (∃ v ∈ S o, x v = true) := fun o x => hout o x
  have hout_rep : ∀ o : Fin m, ∃ i, repF gates n (Fv gates n (out o)) = n + i ∧ i ∈ T gates n m out ∧
      Fv gates n (n + i) = Fv gates n (out o) := by
    intro o
    obtain ⟨u0, hu0⟩ : (S o).Nonempty := Finset.card_pos.mp (by have := hS o; omega)
    have hnv : ¬ ∃ v : Fin n, Fv gates n (out o) = fun x => x v := by
      rintro ⟨v, hv⟩
      obtain ⟨u, hu, huv⟩ := Finset.exists_mem_ne (s := S o) (by have := hS o; omega) v
      have h1 := congrFun hv (fun t => decide (t = u))
      rw [hφ] at h1
      have hvu : ¬ v = u := fun h => huv h.symm
      simp only [decide_eq_true_eq, hvu, decide_false] at h1
      exact absurd ⟨u, hu, rfl⟩ (of_decide_eq_false h1)
    have hT : Fv gates n (out o) (fun _ => true) = true := by
      rw [hφ]; exact decide_eq_true ⟨u0, hu0, rfl⟩
    have hF0 : Fv gates n (out o) (fun _ => false) = false := by
      rw [hφ]; simp
    have hge : n ≤ out o := by
      by_contra h0
      exact hnv ⟨⟨out o, by omega⟩, Fv_input gates n (out o) (by omega)⟩
    have hlt : out o - n < gates.length := by
      by_contra h0
      have := val_oob gates n (fun _ => true) (out o) (by omega)
      simp only [Fv] at hT
      rw [this] at hT
      exact absurd hT (by decide)
    obtain ⟨i, hi, -, hiL, hFi, hmin⟩ := repF_gate gates n _ hnv (out o - n) hlt
      (by rw [show n + (out o - n) = out o by omega])
    have hri : IsRep gates n i := ⟨hiL, ⟨fun _ => true, fun _ => false, by rw [hFi, hT, hF0]; simp⟩,
      fun v hv => hnv ⟨v, by rw [← hFi]; exact hv⟩, fun i' hi' h' => hmin i' hi' (h'.trans hFi)⟩
    exact ⟨i, hi, (mem_T gates n m out i).mpr ⟨hiL, (need_unfold gates n m out i).mpr
      ⟨hri, Or.inl ⟨o, hFi.symm⟩⟩⟩, hFi⟩
  have hTpos : 0 < (T gates n m out).card := by
    obtain ⟨i, -, hi, -⟩ := hout_rep ⟨0, hm⟩
    exact Finset.card_pos.mpr ⟨i, hi⟩
  have hglpos : 0 < (gl gates n m out).length := by rw [gl_length]; exact hTpos
  let κ : Fin 1 → Fin (gl gates n m out).length := fun _ =>
    if h : (ι 0).val ∈ T gates n m out then
      ⟨pos gates n m out (ι 0).val, by rw [gl_length]; exact pos_lt gates n m out _ h⟩
    else ⟨0, hglpos⟩
  let f : Fin (gl gates n m out).length → Fin gates.length := fun q =>
    ⟨((iso gates n m out) ⟨q.val, by rw [← gl_length]; exact q.isLt⟩).val,
      ((mem_T gates n m out _).mp ((iso gates n m out) _).prop).1⟩
  let J : Finset (Fin (gl gates n m out).length) := Finset.univ.filter fun q =>
    (((gl gates n m out).get q).op = GateOp.and ∨ ((gl gates n m out).get q).op = GateOp.or) ∧
      ((gl gates n m out).get q).inputs.length = 2
  refine ⟨gl gates n m out, fun o => sig gates n m out (repF gates n (Fv gates n (out o))), κ, J,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- gate shapes
    intro h hh
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hh
    obtain ⟨j, g, -, -, hg, he⟩ := gl_spec gates n m out q hq
    rw [he]
    have := hgates g (List.mem_of_getElem? hg)
    simpa using this
  · -- the one NOT
    intro q3 hq3
    refine ⟨0, ?_⟩
    obtain ⟨j, g, hjT, hpos, hg, he⟩ := gl_spec gates n m out q3.val q3.isLt
    rw [List.get_eq_getElem, he] at hq3
    have hjL := ((mem_T gates n m out j).mp hjT).1
    have hgj : gates.get ⟨j, hjL⟩ = g := by
      rw [List.get_eq_getElem]; exact Option.some.inj ((List.getElem?_eq_getElem hjL).symm.trans hg)
    obtain ⟨r, hr⟩ := hι ⟨j, hjL⟩ (by rw [hgj]; exact hq3)
    have hr0 : r = 0 := Subsingleton.elim r 0
    subst hr0
    have hι0 : (ι 0).val = j := by rw [hr]
    simp only [κ, hι0, hjT, ↓reduceDIte]
    exact Fin.ext hpos
  · intro q4 hq4
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hq4
  · -- counting
    apply Finset.card_le_card_of_injOn f
    · intro q hq
      simp only [J, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq
      apply hI
      obtain ⟨j, g, hjT, hpos, hg, he⟩ := gl_spec gates n m out q.val q.isLt
      rw [List.get_eq_getElem, he] at hq
      have hfj : (f q).val = j := by
        have := iso_pos gates n m out j hjT
        simp only [f]
        rw [← this]
        congr 2
        exact Fin.ext hpos.symm
      have hgj : gates.get (f q) = g := by
        rw [List.get_eq_getElem]
        have hjL := ((mem_T gates n m out j).mp hjT).1
        exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (by rw [hfj]; exact hg))
      rw [hgj]
      simpa using hq
    · intro a _ b _ hab
      have h1 : ((iso gates n m out) ⟨a.val, by rw [← gl_length]; exact a.isLt⟩).val =
          ((iso gates n m out) ⟨b.val, by rw [← gl_length]; exact b.isLt⟩).val := congrArg Fin.val hab
      have h2 := (iso gates n m out).injective (Subtype.ext h1)
      have h3 := congrArg Fin.val h2
      simp only at h3
      exact Fin.ext h3
  · -- outputs
    intro o x
    obtain ⟨i, hi, hiT, hFi⟩ := hout_rep o
    rw [eval_eq_val]
    show val (gl gates n m out) n x (sig gates n m out (repF gates n (Fv gates n (out o)))) = _
    rw [hi, sig_val gates n m out hgates _ (Or.inr ⟨i, rfl, hiT⟩) x, hFi]
    exact hφ o x
  · -- non constant
    intro jr
    obtain ⟨j, g, hjT, hpos, hg, -⟩ := gl_spec gates n m out jr.val jr.isLt
    have hr := ((need_unfold gates n m out j).mp ((mem_T gates n m out j).mp hjT).2).1
    obtain ⟨x, y, hxy⟩ := hr.2.1
    refine ⟨x, y, ?_⟩
    rw [eval_eq_val, eval_eq_val, ← hpos, gl_val gates n m out hgates x j hjT,
      gl_val gates n m out hgates y j hjT]
    exact hxy
  · -- differs from every earlier wire
    intro jr2 wr hwr
    obtain ⟨j, g, hjT, hpos, hg, -⟩ := gl_spec gates n m out jr2.val jr2.isLt
    have hr := ((need_unfold gates n m out j).mp ((mem_T gates n m out j).mp hjT).2).1
    by_contra hcon
    simp only [not_exists, not_not, eval_eq_val] at hcon
    rw [← hpos] at hcon
    by_cases hwn : wr < n
    · apply hr.2.2.1 ⟨wr, hwn⟩
      funext x
      rw [← gl_val gates n m out hgates x j hjT, hcon x, val_input _ n x wr hwn]
    · have hq' : wr - n < (gl gates n m out).length := by
        have := jr2.isLt; omega
      obtain ⟨j', g', hj'T, hpos', -, -⟩ := gl_spec gates n m out (wr - n) hq'
      have hj'j : j' < j := by
        by_contra hge
        rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
        · have := pos_strict gates n m out j j' hjT hj'T hlt
          omega
        · subst heq; omega
      apply hr.2.2.2 j' hj'j
      funext x
      rw [← gl_val gates n m out hgates x j hjT, ← gl_val gates n m out hgates x j' hj'T, hcon x,
        hpos', show n + (wr - n) = wr by omega]
  · -- every gate is used
    intro jr3
    obtain ⟨j, g, hjT, hpos, hg, -⟩ := gl_spec gates n m out jr3.val jr3.isLt
    obtain ⟨hjL, hneed⟩ := (mem_T gates n m out j).mp hjT
    rcases ((need_unfold gates n m out j).mp hneed) with ⟨hr, ⟨o, ho⟩ | ⟨k, hjk, hkL, hneedk, g', hg', a, ha, hrd⟩⟩
    · left
      refine ⟨o, ?_⟩
      simp only
      rw [ho, rep_self gates n j hr, sig_gate, hpos]
    · right
      have hkT : k ∈ T gates n m out := (mem_T gates n m out k).mpr ⟨hkL, hneedk⟩
      have hkq : pos gates n m out k < (gl gates n m out).length := by
        rw [gl_length]; exact pos_lt gates n m out k hkT
      refine ⟨⟨pos gates n m out k, hkq⟩, ?_⟩
      obtain ⟨k', g'', hk'T, hpos', hg'', he⟩ := gl_spec gates n m out _ hkq
      have hkk : k' = k := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := pos_strict gates n m out _ _ hk'T hkT h; omega
        · have := pos_strict gates n m out _ _ hkT hk'T h; omega
      subst hkk
      have hgg : g'' = g' := Option.some.inj (hg''.symm.trans hg')
      subst hgg
      rw [List.get_eq_getElem, he]
      rcases (hgates g'' (List.mem_of_getElem? hg'')).1 with hop | hop | hop
      · right
        refine ⟨Or.inl hop, ?_⟩
        rw [rel_ao g'' (Or.inl hop)] at ha
        simp only [List.mem_map]
        exact ⟨a, ha, by rw [hrd, sig_gate, hpos]⟩
      · right
        refine ⟨Or.inr hop, ?_⟩
        rw [rel_ao g'' (Or.inr hop)] at ha
        simp only [List.mem_map]
        exact ⟨a, ha, by rw [hrd, sig_gate, hpos]⟩
      · left
        refine ⟨hop, ?_⟩
        rw [rel_not g'' hop] at ha
        rcases hin : g''.inputs with _ | ⟨b, rest⟩
        · rw [hin] at ha; simp at ha
        · rw [hin] at ha
          simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at ha
          subst ha
          simp only [List.map_cons, List.head?_cons]
          rw [hrd, sig_gate, hpos]
  · -- two different inputs
    intro jr4 hop
    obtain ⟨j, g, hjT, -, hg, he⟩ := gl_spec gates n m out jr4.val jr4.isLt
    have hr := ((need_unfold gates n m out j).mp ((mem_T gates n m out j).mp hjT).2).1
    rw [List.get_eq_getElem, he] at hop ⊢
    have hlen := (hgates g (List.mem_of_getElem? hg)).2
    obtain ⟨a, b, hin, ha, hb, hab⟩ := rep_ao gates n j g hg hr hop hlen
    have hrel := rel_ao g hop
    refine ⟨sig gates n m out (repF gates n (eff gates n j a)),
      sig gates n m out (repF gates n (eff gates n j b)), ?_, by rw [hin]; rfl⟩
    intro heq
    apply hab
    funext x
    rw [← read_val gates n m out hgates j hjT g hg a (by rw [hrel, hin]; simp) ha x,
      ← read_val gates n m out hgates j hjT g hg b (by rw [hrel, hin]; simp) hb x, heq]

end PEqualNP.Outside.L_meta_1346

theorem PEqualNP.Outside.L_meta_1346 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ ic : Fin m, 2 ≤ (S ic).card) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ ι : Fin 1 → Fin gates.length, (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin 1, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → (∃ c : PEqualNP.CircuitLowerBounds.GateOp, (c = PEqualNP.CircuitLowerBounds.GateOp.and ∨ c = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (o1 : Fin m) (x1 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set (ι 0).val ⟨c, []⟩, out o1⟩ (List.ofFn x1) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o1⟩ (List.ofFn x1)) ∨ ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin 1 → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin 1, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card ≤ I.card ∧ (∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, x2 v2 = true)) ∧ (∀ jr : Fin gl.length, ∃ xr yr : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn xr) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr.val⟩ (List.ofFn yr)) ∧ (∀ jr2 : Fin gl.length, ∀ wr : ℕ, wr < n + jr2.val → ∃ xr2 : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, n + jr2.val⟩ (List.ofFn xr2) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, wr⟩ (List.ofFn xr2)) ∧ (∀ jr3 : Fin gl.length, (∃ oq : Fin m, ol oq = n + jr3.val) ∨ ∃ kr : Fin gl.length, ((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gl.get kr).inputs.head? = some (n + jr3.val)) ∨ (((gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get kr).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ n + jr3.val ∈ (gl.get kr).inputs)) ∧ (∀ jr4 : Fin gl.length, ((gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get jr4).op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ ar br : ℕ, ar ≠ br ∧ (gl.get jr4).inputs = [ar, br]) := by
  intro n m S hS gates out hgates hout ι hι I hI
  exact PEqualNP.Outside.L_meta_1346.main n m S hS gates out hgates hout ι hι I hI
