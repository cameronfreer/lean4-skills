-- Compile-check for the exact Lean snippets the references ship (#188 / #162
-- / the #200 reference audit). Requires a Mathlib project; run from one:
--
--   lake env lean /path/to/lean4-skills/plugins/lean4/tests/fixtures/reference_snippets/measure_theory_snippets.lean
--
-- Not wired into CI (CI has no Mathlib). Last checked against Mathlib commit
-- de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11 (Lean 4.34.0-rc1, local checkout):
-- exit 0 — see the PR #200 body. If you change one of the documented snippets,
-- change it here too and re-run. Negative controls are `#guard_msgs` blocks: the
-- file fails if a documented failure stops failing or its message drifts.
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order
import Mathlib.Tactic

open MeasureTheory

-- measure-theory.md § condExpWith: optional σ-finiteness freeze via plain `have`
-- (plain `have` registers the instance; `haveI` would only inline).
example {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) : True := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  trivial

-- measure-theory.md § Set-Integral Projection: the wrapper, with a NAMED ambient
-- space (never `‹_›`, which resolves to `m` itself), `MeasurableSet[m] s`, and the
-- finite-measure assumption that supplies `SigmaFinite (μ.trim hm)`.
lemma setIntegral_condExp_eq {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {s : Set Ω} (hs : MeasurableSet[m] s) {g : Ω → ℝ} (hg : Integrable g μ) :
    ∫ x in s, (μ[g|m]) x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_condExp hm hg hs

-- measure-theory.md § Manual instances: probability pushforward.
example {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → β} (hf : AEMeasurable f μ) : True := by
  have : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf
  trivial

-- measure-theory.md lemma list: a.e.-strong measurability of the CE.
example {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
    {m : MeasurableSpace Ω} {f : Ω → ℝ} : AEStronglyMeasurable[m] (μ[f | m]) μ :=
  stronglyMeasurable_condExp.aestronglyMeasurable

-- lean-phrasebook.md § Goal Manipulation.
example : True ∧ True := by
  constructor
  swap
  all_goals trivial

example : True ∧ True ∧ True := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left 1
  pick_goal 2
  all_goals trivial

-- compilation-errors.md: termination_by (Lean ≥ 4.6 syntax).
def my_rec : Nat → Nat
  | 0 => 0
  | n + 1 => my_rec n
termination_by n => n

-- compilation-errors.md / tactics-reference.md: infer_instance.
example : Nonempty Nat := by infer_instance

-- Missing-instance recipes (compiler-guided-repair.md, command-examples.md,
-- review.md): `borel β` is a valid supplied value ONLY given a topology, and
-- only when the Borel σ-algebra is the intended structure.
example {β : Type*} [TopologicalSpace β] : True := by
  have : MeasurableSpace β := borel β
  trivial

-- agent-workflows.md repair example: `DiscreteTopology α` needs EVIDENCE that
-- the ambient topology is `⊥`; `⟨rfl⟩` proves it only when it literally is.
example {α : Type*} [t : TopologicalSpace α] (hdisc : t = ⊥) {β : Type*}
    [TopologicalSpace β] (f : α → β) : Continuous f := by
  have : DiscreteTopology α := ⟨hdisc⟩
  exact continuous_of_discreteTopology

-- ❌ Negative control (executable): `⟨rfl⟩` does not elaborate for an arbitrary `t`.
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  t = ⊥
in the application
  { eq_bot := rfl }
-/
#guard_msgs in
example {α : Type*} [t : TopologicalSpace α] : DiscreteTopology α := ⟨rfl⟩

-- measure-theory.md § σ-Algebra Relations (Ready-to-Paste), with DISTINCT
-- Ω β γ and NAMED ambient structures. `MeasurableSpace.comap Z m` pulls the
-- CODOMAIN structure `m : MeasurableSpace β` back along `Z : Ω → β`; the joint
-- σ-algebra uses the product structure on the codomain of the pair.
example {Ω β γ : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (Z : Ω → β) (W : Ω → γ) (hZ : Measurable Z)
    (hW : Measurable W) (μ : Measure Ω) (f : Ω → ℝ) : True := by
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W mγ
  let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω ↦ (Z ω, W ω)) (mβ.prod mγ)
  -- σ(W) ≤ ambient
  have hmW_le : mW ≤ mΩ := hW.comap_le
  -- σ(Z,W) ≤ ambient
  have hmZW_le : mZW ≤ mΩ := (hZ.prodMk hW).comap_le
  -- σ(W) ≤ σ(Z,W): W = Prod.snd ∘ (Z,W)
  have hmW_le_mZW : mW ≤ mZW :=
    MeasurableSpace.comap_le_comap_of_eq_comp Prod.snd measurable_snd rfl
  -- Measurability transport. The ambient fact names `mΩ` explicitly: after the
  -- two `let`s, a bare `StronglyMeasurable` resolves to the NEWEST class-typed
  -- local (`mZW`), and `hsm_ce.mono hmW_le` then fails with "expected mW ≤ mZW"
  -- — the drift trap, live.
  have hsm_ce : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condExp
  have hsm_ceAmb : StronglyMeasurable[mΩ] (μ[f|mW]) := hsm_ce.mono hmW_le
  trivial

-- The pre-review proof of σ(W) ≤ σ(Z,W) was
-- `(measurable_snd.comp (hZ.prod_mk hW)).comap_le`; besides the stale name,
-- it proves `comap W mγ ≤ mΩ` (a bound against the AMBIENT space), not `mW ≤ mZW`.
example {Ω β γ : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (Z : Ω → β) (W : Ω → γ) (hZ : Measurable Z)
    (hW : Measurable W) : MeasurableSpace.comap W mγ ≤ mΩ :=
  (measurable_snd.comp (hZ.prodMk hW)).comap_le

-- ❌ Negative control (executable): comap with the DOMAIN structure is a type error.
/--
error: Application type mismatch: The argument
  mΩ
has type
  MeasurableSpace.{u_1} Ω
of sort `Type u_1` but is expected to have type
  MeasurableSpace.{u_2} β
of sort `Type u_2` in the application
  MeasurableSpace.comap Z mΩ
-/
#guard_msgs in
example {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β] (Z : Ω → β) : True := by
  let _bad : MeasurableSpace Ω := MeasurableSpace.comap Z mΩ
  trivial

-- ❌ Negative control (executable): `SigmaFinite μ` alone does NOT give
-- `SigmaFinite (μ.trim hm)` by synthesis — the summaries say `[IsFiniteMeasure μ]`
-- for a reason (`sigmaFinite_trim_bot_iff` shows the general statement fails).
/--
error: failed to synthesize instance of type class
  SigmaFinite (μ.trim hm)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [SigmaFinite μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) : True := by
  have : SigmaFinite (μ.trim hm) := inferInstance
  trivial

-- instance-pollution.md Solution 2 / measure-theory.md three-tier recipe, with
-- the ambient instance as a NAMED PARAMETER (not a `let`): `hZ` already has the
-- `@Measurable Ω β m0 _ Z` type, and the Tier-3 ambient fact keeps the structure
-- explicit with `MeasurableSet[m0]` (a bare `MeasurableSet` selects the newest
-- local, mZW).
example {Ω β γ : Type*} [m0 : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (Z : Ω → β) (W : Ω → γ) (hZ : Measurable Z)
    (hW : Measurable W) (B : Set β) (hB : MeasurableSet B) : True := by
  have hZ_m0 : @Measurable Ω β m0 _ Z := hZ
  have hBpre_m0 : @MeasurableSet Ω m0 (Z ⁻¹' B) := hB.preimage hZ_m0
  let mW  : MeasurableSpace Ω := MeasurableSpace.comap W mγ
  let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω ↦ (Z ω, W ω)) (mβ.prod mγ)
  have hmW_le : mW ≤ m0 := hW.comap_le
  have hBpre : MeasurableSet[m0] (Z ⁻¹' B) := hBpre_m0
  trivial

-- ❌ Negative control (executable): `simpa [m0]` with `m0` a parameter.
/--
error: Invalid argument: Variable `m0` is not a proposition or let-declaration
-/
#guard_msgs in
example {Ω β : Type*} [m0 : MeasurableSpace Ω] [MeasurableSpace β]
    (Z : Ω → β) (hZ : Measurable Z) : True := by
  have hZ_m0 : @Measurable Ω β m0 _ Z := by simpa [m0] using hZ
  trivial

-- ❌ Negative control (executable): the transport line with a BARE
-- `StronglyMeasurable` — after the two `let`s it resolves to mZW, so
-- `hsm_ce.mono hmW_le` is handed `mW ≤ mΩ` where `mW ≤ mZW` is expected.
/--
error: Application type mismatch: The argument
  hmW_le
has type
  mW ≤ mΩ
but is expected to have type
  mW ≤ mZW
in the application
  StronglyMeasurable.mono hsm_ce hmW_le
-/
#guard_msgs in
example {Ω β γ : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    [mγ : MeasurableSpace γ] (Z : Ω → β) (W : Ω → γ) (hW : Measurable W)
    (μ : Measure Ω) (f : Ω → ℝ) : True := by
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W mγ
  let mZW : MeasurableSpace Ω := MeasurableSpace.comap (fun ω ↦ (Z ω, W ω)) (mβ.prod mγ)
  have hmW_le : mW ≤ mΩ := hW.comap_le
  have hsm_ce : StronglyMeasurable[mW] (μ[f|mW]) := stronglyMeasurable_condExp
  have hsm_ceAmb : StronglyMeasurable (μ[f|mW]) := hsm_ce.mono hmW_le
  trivial
