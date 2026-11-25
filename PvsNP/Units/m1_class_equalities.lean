import Mathlib
import PvsNP.Defs
import CookLevin

namespace PvsNP.Units.m1_class_equalities

/-- The bridge hypothesis, stated once for the helpers below. -/
abbrev Bridge : Prop :=
  ∀ {α β A B : Type} [Finite A] [Finite B] (ea : α → List A) (eb : β → List B) (f : α → β),
    PvsNP.SingleTape.PolyTimeComputable ea eb f ↔ PvsNP.PolyTimeComputable ea eb f

/-- Given the bridge, single-tape P is TM2 P: a decider is poly-time on one side exactly when
it is on the other, and the rest of the definition is the same on both sides. -/
theorem singleTape_P_eq (h : Bridge) : PvsNP.SingleTape.P = PvsNP.P := by
  ext L
  constructor
  · rintro ⟨f, hf, hdec⟩
    exact ⟨f, (h PvsNP.encodeString PvsNP.encodeAnswer f).mp hf, hdec⟩
  · rintro ⟨f, hf, hdec⟩
    exact ⟨f, (h PvsNP.encodeString PvsNP.encodeAnswer f).mpr hf, hdec⟩

/-- Given the bridge, single-tape NP is TM2 NP: a verifier is poly-time on one side exactly
when it is on the other, and the certificate condition is the same on both sides. -/
theorem singleTape_NP_eq (h : Bridge) : PvsNP.SingleTape.NP = PvsNP.NP := by
  ext L
  constructor
  · rintro ⟨V, p, hV, hcond⟩
    exact ⟨V, p, (h PvsNP.encodePair PvsNP.encodeAnswer V).mp hV, hcond⟩
  · rintro ⟨V, p, hV, hcond⟩
    exact ⟨V, p, (h PvsNP.encodePair PvsNP.encodeAnswer V).mpr hV, hcond⟩

/-- coNP follows from NP: the complement of a language is in single-tape NP exactly when it is
in TM2 NP. -/
theorem singleTape_coNP_eq (hNP : PvsNP.SingleTape.NP = PvsNP.NP) :
    PvsNP.SingleTape.coNP = PvsNP.coNP := by
  ext L
  show Lᶜ ∈ PvsNP.SingleTape.NP ↔ Lᶜ ∈ PvsNP.NP
  rw [hNP]

/-- Given the bridge, single-tape Karp reducibility is TM2 Karp reducibility. -/
theorem karpReducible_iff (h : Bridge) (L₁ L₂ : Language Bool) :
    PvsNP.SingleTape.KarpReducible L₁ L₂ ↔ PvsNP.KarpReducible L₁ L₂ := by
  constructor
  · rintro ⟨f, hf, hcond⟩
    exact ⟨f, (h PvsNP.encodeString PvsNP.encodeString f).mp hf, hcond⟩
  · rintro ⟨f, hf, hcond⟩
    exact ⟨f, (h PvsNP.encodeString PvsNP.encodeString f).mpr hf, hcond⟩

/-- Given the NP equality and the Karp-reducibility equivalence, single-tape NP-hardness is
TM2 NP-hardness. -/
theorem npHard_iff (hNP : PvsNP.SingleTape.NP = PvsNP.NP)
    (hKarp : ∀ L₁ L₂ : Language Bool,
      PvsNP.SingleTape.KarpReducible L₁ L₂ ↔ PvsNP.KarpReducible L₁ L₂)
    (L₂ : Language Bool) :
    PvsNP.SingleTape.NPHard L₂ ↔ PvsNP.NPHard L₂ := by
  constructor
  · intro hh L' hL'
    rw [← hNP] at hL'
    exact (hKarp L' L₂).mp (hh L' hL')
  · intro hh L' hL'
    rw [hNP] at hL'
    exact (hKarp L' L₂).mpr (hh L' hL')

/-- Given the NP equality and the NP-hardness equivalence, single-tape NP-completeness is
TM2 NP-completeness. -/
theorem npComplete_iff (hNP : PvsNP.SingleTape.NP = PvsNP.NP)
    (hHard : ∀ L₂ : Language Bool,
      PvsNP.SingleTape.NPHard L₂ ↔ PvsNP.NPHard L₂)
    (L₂ : Language Bool) :
    PvsNP.SingleTape.NPComplete L₂ ↔ PvsNP.NPComplete L₂ := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (hHard L₂).mp h2⟩
    rw [hNP] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, (hHard L₂).mpr h2⟩
    rw [← hNP] at h1
    exact h1

end PvsNP.Units.m1_class_equalities

/-- Bridge: given the two simulations, the single-tape classes are the TM2 classes. -/
theorem PvsNP.Units.m1_class_equalities
    (h : ∀ {α β A B : Type} [Finite A] [Finite B] (ea : α → List A) (eb : β → List B)
      (f : α → β),
      PvsNP.SingleTape.PolyTimeComputable ea eb f ↔ PvsNP.PolyTimeComputable ea eb f) :
    PvsNP.SingleTape.P = PvsNP.P ∧ PvsNP.SingleTape.NP = PvsNP.NP ∧
      PvsNP.SingleTape.coNP = PvsNP.coNP ∧
      ∀ L₁ L₂ : Language Bool,
        (PvsNP.SingleTape.KarpReducible L₁ L₂ ↔ PvsNP.KarpReducible L₁ L₂) ∧
        (PvsNP.SingleTape.NPHard L₂ ↔ PvsNP.NPHard L₂) ∧
        (PvsNP.SingleTape.NPComplete L₂ ↔ PvsNP.NPComplete L₂) := by
  have hP := PvsNP.Units.m1_class_equalities.singleTape_P_eq h
  have hNP := PvsNP.Units.m1_class_equalities.singleTape_NP_eq h
  have hcoNP := PvsNP.Units.m1_class_equalities.singleTape_coNP_eq hNP
  refine ⟨hP, hNP, hcoNP, fun L₁ L₂ => ⟨?_, ?_, ?_⟩⟩
  · exact PvsNP.Units.m1_class_equalities.karpReducible_iff h L₁ L₂
  · exact PvsNP.Units.m1_class_equalities.npHard_iff hNP
      (fun a b => PvsNP.Units.m1_class_equalities.karpReducible_iff h a b) L₂
  · exact PvsNP.Units.m1_class_equalities.npComplete_iff hNP
      (fun a => PvsNP.Units.m1_class_equalities.npHard_iff hNP
        (fun x y => PvsNP.Units.m1_class_equalities.karpReducible_iff h x y) a) L₂
