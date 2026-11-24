import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2864_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Le (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem le_refl (w : List Bool) : Le w w := ⟨rfl, fun _ h => h⟩

theorem le_append {a a' b b' : List Bool} (ha : Le a a') (hb : Le b b') : Le (a ++ b) (a' ++ b') := by
  refine ⟨by simp [ha.1, hb.1], fun i hi => ?_⟩
  by_cases h : i < a.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (ha.1 ▸ h)]
    exact ha.2 i hi
  · have h' : a.length ≤ i := Nat.le_of_not_lt h
    rw [List.getD_append_right _ _ _ _ h'] at hi
    rw [List.getD_append_right _ _ _ _ (ha.1 ▸ h'), ← ha.1]
    exact hb.2 _ hi

theorem le_false (n : ℕ) (l : List Bool) (hl : l.length = n) : Le (List.replicate n false) l := by
  refine ⟨by simp [hl], fun i hi => ?_⟩
  exfalso
  by_cases h : i < n
  · rw [List.getD_replicate _ h] at hi
    exact Bool.false_ne_true hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.false_ne_true hi

theorem le_true (n : ℕ) (l : List Bool) (hl : l.length = n) : Le l (List.replicate n true) := by
  refine ⟨by simp [hl], fun i hi => ?_⟩
  by_cases h : i < n
  · exact List.getD_replicate _ h
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    exact absurd hi Bool.false_ne_true

theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : Le w w') (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro x ⟨i, hi, rfl⟩
    exact h.2 i (hv _ ⟨i, hi, rfl⟩)
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨x, ⟨i, hi, rfl⟩, hx⟩ := hv
    exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hx⟩

theorem le_step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : Le w w') :
    Le (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := by
  refine le_append h ⟨rfl, fun i hi => ?_⟩
  by_cases h0 : i = 0
  · subst h0
    simp only [List.getD_cons_zero] at hi ⊢
    exact gate_mono g hg h hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi Bool.false_ne_true

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, Le w w' →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (le_step g (hgs g List.mem_cons_self) h)

theorem wires_mono {C : Circuit} (hm : Monotone2 C) {u u' : List Bool} (h : Le u u') (i : ℕ)
    (hi : (C.wires u).getD i false = true) : (C.wires u').getD i false = true := by
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  exact (fold_mono C.gates hgs u u' h).2 i hi

def LD (C : Circuit) (N w : ℕ) : Prop :=
  ∃ x : Fin N → Bool, (C.wires (List.ofFn x ++ List.replicate N false)).getD w false ≠
    (C.wires (List.ofFn x ++ List.replicate N true)).getD w false

def PD (C : Circuit) (N w : ℕ) : Prop :=
  ∃ y : Fin N → Bool, (C.wires (List.replicate N false ++ List.ofFn y)).getD w false ≠
    (C.wires (List.replicate N true ++ List.ofFn y)).getD w false

theorem indL {C : Circuit} (hm : Monotone2 C) {N w : ℕ} (h : ¬ LD C N w) (x y : Fin N → Bool) :
    (C.wires (List.ofFn x ++ List.ofFn y)).getD w false =
      (C.wires (List.ofFn x ++ List.replicate N false)).getD w false := by
  have heq : (C.wires (List.ofFn x ++ List.replicate N false)).getD w false =
      (C.wires (List.ofFn x ++ List.replicate N true)).getD w false := by
    by_contra hne
    exact h ⟨x, hne⟩
  have h1 := wires_mono hm (le_append (le_refl (List.ofFn x)) (le_false N (List.ofFn y) (by simp))) w
  have h2 := wires_mono hm (le_append (le_refl (List.ofFn x)) (le_true N (List.ofFn y) (by simp))) w
  cases hmid : (C.wires (List.ofFn x ++ List.ofFn y)).getD w false
  · cases hlo : (C.wires (List.ofFn x ++ List.replicate N false)).getD w false
    · rfl
    · rw [h1 hlo] at hmid
      exact absurd hmid (by decide)
  · rw [heq]
    exact (h2 hmid).symm

theorem indP {C : Circuit} (hm : Monotone2 C) {N w : ℕ} (h : ¬ PD C N w) (x y : Fin N → Bool) :
    (C.wires (List.ofFn x ++ List.ofFn y)).getD w false =
      (C.wires (List.replicate N false ++ List.ofFn y)).getD w false := by
  have heq : (C.wires (List.replicate N false ++ List.ofFn y)).getD w false =
      (C.wires (List.replicate N true ++ List.ofFn y)).getD w false := by
    by_contra hne
    exact h ⟨y, hne⟩
  have h1 := wires_mono hm (le_append (le_false N (List.ofFn x) (by simp)) (le_refl (List.ofFn y))) w
  have h2 := wires_mono hm (le_append (le_true N (List.ofFn x) (by simp)) (le_refl (List.ofFn y))) w
  cases hmid : (C.wires (List.ofFn x ++ List.ofFn y)).getD w false
  · cases hlo : (C.wires (List.replicate N false ++ List.ofFn y)).getD w false
    · rfl
    · rw [h1 hlo] at hmid
      exact absurd hmid (by decide)
  · rw [heq]
    exact (h2 hmid).symm

theorem star (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (hq : 0 < q)
    (hlin : ∀ (p p' : Fin N), p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hsound : ∀ (z : Fin (N + N) → Bool),
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬∃ (p : Fin N) (l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false)
    (u v : (Fin N → Bool) → Bool)
    (hacc : ∀ (p l : Fin N), (u (fun j => decide (j = p)) && v (fun j => decide (j = l))) = true →
      circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
    (p p' l l' : Fin N)
    (h1 : (u (fun j => decide (j = p)) && v (fun j => decide (j = l))) = true)
    (h2 : (u (fun j => decide (j = p')) && v (fun j => decide (j = l'))) = true) :
    p = p' ∨ l = l' := by
  have inc : ∀ p0 l0 : Fin N,
      (u (fun j => decide (j = p0)) && v (fun j => decide (j = l0))) = true → I p0 l0 := by
    intro p0 l0 h
    by_contra hI
    have hC := hacc p0 l0 h
    have hne1 : ∀ a b : Fin N, Fin.natAdd N a ≠ Fin.castAdd N b := by
      intro a b hab
      have := congrArg Fin.val hab
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    have hF := hsound (fun k => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)) ?_ ?_
    · rw [hF] at hC
      exact Bool.false_ne_true hC
    · have hsub : Subsingleton { l1 : Fin N //
          (fun k => decide (k = Fin.castAdd N p0 ∨ k = Fin.natAdd N l0)) (Fin.natAdd N l1) = true } := by
        refine ⟨fun a b => Subtype.ext ?_⟩
        have ha := a.2
        have hb := b.2
        simp only [decide_eq_true_eq] at ha hb
        have ha' : a.1 = l0 := by
          rcases ha with ha | ha
          · exact absurd ha (hne1 _ _)
          · exact Fin.natAdd_injective _ _ ha
        have hb' : b.1 = l0 := by
          rcases hb with hb | hb
          · exact absurd hb (hne1 _ _)
          · exact Fin.natAdd_injective _ _ hb
        rw [ha', hb']
      exact le_trans (Fintype.card_le_one_iff_subsingleton.mpr hsub) hq
    · rintro ⟨p1, l1, hI1, hz1, hz2⟩
      simp only [decide_eq_true_eq] at hz1 hz2
      have hp : p1 = p0 := by
        rcases hz1 with hz1 | hz1
        · exact Fin.castAdd_injective _ _ hz1
        · exact absurd hz1.symm (hne1 _ _)
      have hl : l1 = l0 := by
        rcases hz2 with hz2 | hz2
        · exact absurd hz2 (hne1 _ _)
        · exact Fin.natAdd_injective _ _ hz2
      rw [hp, hl] at hI1
      exact hI hI1
  simp only [Bool.and_eq_true] at h1 h2
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hpp, hll⟩ := hne
  have i1 := inc p l (by simp [h1.1, h1.2])
  have i2 := inc p l' (by simp [h1.1, h2.2])
  have i3 := inc p' l (by simp [h2.1, h1.2])
  have i4 := inc p' l' (by simp [h2.1, h2.2])
  obtain ⟨l0, _, huniq⟩ := hlin p p' hpp
  exact hll ((huniq l ⟨i1, i3⟩).trans (huniq l' ⟨i2, i4⟩).symm)

end PEqualNP.Outside.L_meta_2864_aux

open PEqualNP.Outside.L_meta_2864_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2864 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) →       PEqualNP.MetaComplexity.Monotone2 x5 →         (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x9 = Bool.false) →           ∀ (x10 x11 : ℕ),             ¬((∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.false)).getD x12 Bool.false ≠ (x5.wires (List.ofFn x14 ++ List.replicate x2 Bool.true)).getD x12 Bool.false) ∨ ∀ x12 ∈ [x10, x11], ∃ (x14 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x14)).getD x12 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x14)).getD x12 Bool.false) →               have x13 : ℕ → (Fin x2 → Bool) → (Fin x2 → Bool) → Bool := fun (x13 : ℕ) (x14 x15 : Fin x2 → Bool) => (x5.wires (List.ofFn x14 ++ List.ofFn x15)).getD x13 Bool.false;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               (∃ x15 ∈ [x10, x11], ∀ (x16 x17 : Fin x2 → Bool), (x13 x10 x16 x17 && x13 x11 x16 x17) = x13 x15 x16 x17) ∨ ∃ (x15 : (Fin x2 → Bool) → Bool) (x16 : (Fin x2 → Bool) → Bool), (∀ (x17 x18 : Fin x2 → Bool), (x13 x10 x17 x18 && x13 x11 x17 x18) = (x15 x17 && x16 x18)) ∧ ((∀ (x17 x18 : Fin x2), (x15 (x14 x17) && x16 (x14 x18)) = Bool.true → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x20 : Fin (x2 + x2)) => Decidable.decide (x20 = Fin.castAdd x2 x17 ∨ x20 = Fin.natAdd x2 x18)) = Bool.true) → ∀ (x18 x19 x20 x21 : Fin x2), (x15 (x14 x18) && x16 (x14 x20)) = Bool.true → (x15 (x14 x19) && x16 (x14 x21)) = Bool.true → x18 = x19 ∨ x20 = x21) := by
  intro q N I _ C hq hlin hmono hsound a b hbad
  have hbad1 : ¬ (LD C N a ∧ LD C N b) := by
    rintro ⟨h1, h2⟩
    refine hbad (Or.inl ?_)
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1
    · exact h2
  have hbad2 : ¬ (PD C N a ∧ PD C N b) := by
    rintro ⟨h1, h2⟩
    refine hbad (Or.inr ?_)
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact h1
    · exact h2
  have const : ∀ w : ℕ, ¬ LD C N w → ¬ PD C N w → ∀ x y : Fin N → Bool,
      (C.wires (List.ofFn x ++ List.ofFn y)).getD w false =
        (C.wires (List.ofFn (fun _ : Fin N => false) ++ List.ofFn (fun _ : Fin N => false))).getD w false := by
    intro w hL hP x y
    rw [indP hmono hP x y, ← indP hmono hP (fun _ => false) y, indL hmono hL (fun _ => false) y,
      ← indL hmono hL (fun _ => false) (fun _ => false)]
  dsimp only
  by_cases hLa : LD C N a
  · have hLb : ¬ LD C N b := fun h => hbad1 ⟨hLa, h⟩
    by_cases hPa : PD C N a
    · have hPb : ¬ PD C N b := fun h => hbad2 ⟨hPa, h⟩
      left
      cases hc : (C.wires (List.ofFn (fun _ : Fin N => false) ++ List.ofFn (fun _ : Fin N => false))).getD b false
      · exact ⟨b, by simp, fun x y => by rw [const b hLb hPb x y, hc]; simp⟩
      · exact ⟨a, by simp, fun x y => by rw [const b hLb hPb x y, hc]; simp⟩
    · right
      exact ⟨fun x => (C.wires (List.ofFn x ++ List.replicate N false)).getD b false,
        fun y => (C.wires (List.replicate N false ++ List.ofFn y)).getD a false,
        fun x y => by rw [indP hmono hPa x y, indL hmono hLb x y, Bool.and_comm],
        star q N I C hq hlin hsound
          (fun x => (C.wires (List.ofFn x ++ List.replicate N false)).getD b false)
          (fun y => (C.wires (List.replicate N false ++ List.ofFn y)).getD a false)⟩
  · by_cases hPb : PD C N b
    · have hPa : ¬ PD C N a := fun h => hbad2 ⟨h, hPb⟩
      left
      cases hc : (C.wires (List.ofFn (fun _ : Fin N => false) ++ List.ofFn (fun _ : Fin N => false))).getD a false
      · exact ⟨a, by simp, fun x y => by rw [const a hLa hPa x y, hc]; simp⟩
      · exact ⟨b, by simp, fun x y => by rw [const a hLa hPa x y, hc]; simp⟩
    · right
      exact ⟨fun x => (C.wires (List.ofFn x ++ List.replicate N false)).getD a false,
        fun y => (C.wires (List.replicate N false ++ List.ofFn y)).getD b false,
        fun x y => by rw [indL hmono hLa x y, indP hmono hPb x y],
        star q N I C hq hlin hsound
          (fun x => (C.wires (List.ofFn x ++ List.replicate N false)).getD a false)
          (fun y => (C.wires (List.replicate N false ++ List.ofFn y)).getD b false)⟩
