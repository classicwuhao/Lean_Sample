-- This module serves as the root of the `LeanSample` library.
-- Import modules here that should be built as part of the library.
import LeanSample.Basic

variable (A B C D:Prop)

theorem l1 : (A→B) → (B→C) → (A→C) := by
  intros
  apply ‹B→C›
  apply ‹A→B›
  exact ‹A›

theorem l3: A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
  intros
  cases ‹A ∧ (B ∧ C)›
  cases ‹B ∧ C ›
  constructor
  exact And.intro ‹A› ‹B›
  exact ‹C›

theorem l2: A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intros
  cases ‹A ∧ (B ∨ C)›
  cases ‹B ∨ C›
  apply Or.inl
  apply And.intro
  exact ‹A›
  exact ‹B›
  apply Or.inr
  apply And.intro
  exact ‹A›
  exact ‹C›

theorem l4: ((A ∨ B)→C)→((A→C)∨(B→C)) := by
  intros
  rename_i h0
  apply Or.inl
  intros
  rename_i h1
  apply h0
  apply Or.inl
  exact h1

theorem l5: (A→B)→(A→C)→(B→C→D)→A→D := by
  intros
  rename_i h0 h1 h2 h3
  apply h2
  apply h0
  exact h3
  apply h1
  exact h3
  done

theorem l6: ((((A→B)→A)→A)→B)→B := by
  intros
  rename_i h0
  apply h0
  intros
  rename_i h1
  apply h1
  intros
  rename_i h2
  apply h0
  intros
  exact h2
  done

theorem l7: (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intros
  rename_i h0
  cases h0
  rename_i h1 h2
  constructor
  exact h1.left
  constructor
  exact h1.right
  exact h2
  done

theorem l8: ((A ∧ B) → C ) → (A → (B → C)) := by
  intros
  rename_i h0 h1 h2
  apply h0
  exact And.intro h1 h2
  done

theorem l9: (A ∨ B ) ∨ C → A ∨ ( B ∨ C) := by
  intros
  rename_i h0
  cases h0
  rename_i h1
  cases h1 with
  | inl h2 =>
    apply Or.inl
    exact h2
  | inr h3 => exact Or.inr (Or.inl h3)
  rename_i h4
  exact Or.inr (Or.inr h4)
  done
