import MCore.RH.R0.RhoConcrete
import MCore.RH.NB.ZeroLimitFrontier
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace MCore.RH.R2

noncomputable section

/--
The actual final statement of the repository.

This is only a definition of the Riemann hypothesis already provided by the
pinned Mathlib. No inhabitant/proof is asserted here.
-/
def FinalStatement : Prop :=
  RiemannHypothesis

/--
The compressed internal endpoint supplied by the frozen Nyman--Beurling
distance/limit machinery.
-/
def CompressedEndpoint : Prop :=
  MCore.RH.R0.concreteNBData.DNLimit
    MCore.RH.R0.concreteGeneratorFamily = 0

/--
The unique internal open bridge after collapsing the already-certified Lean
wiring: the concrete squared projection defect tends to zero.
-/
def OpenBridge : Prop :=
  MCore.RH.R0.concreteNBData.DNToZero
    MCore.RH.R0.concreteGeneratorFamily

/--
Formal shape of the R1 external interface. Defining this proposition does not
assume it and does not create a project axiom.
-/
def R1ExternalBridge : Prop :=
  CompressedEndpoint ↔ FinalStatement

/--
Frozen NB15 wiring: the internal open bridge is exactly the compressed
DNLimit endpoint. This theorem proves neither side.
-/
theorem openBridge_iff_compressedEndpoint :
    OpenBridge ↔ CompressedEndpoint := by
  simpa [OpenBridge, CompressedEndpoint] using
    (MCore.RH.NB.NBHilbertData.DNToZero_iff_DNLimit_eq_zero
      MCore.RH.R0.concreteNBData
      MCore.RH.R0.concreteGeneratorFamily)

/--
If the separately audited R1 external equivalence is supplied as a hypothesis,
then the compressed Lean wiring composes to the actual final statement.

The external criterion remains explicit in the theorem hypothesis; it is not
introduced as an axiom or theorem of this file.
-/
theorem openBridge_iff_finalStatement_of_r1
    (hR1 : R1ExternalBridge) :
    OpenBridge ↔ FinalStatement := by
  exact openBridge_iff_compressedEndpoint.trans hR1

/--
Generic backward-dense closing lemma.

Any explicit real majorant eps_N which dominates the concrete finite defect
DN_N at every stage and tends to zero forces the internal open bridge.

This theorem is pure order/topology wiring. It does not construct such a
majorant; supplying one unconditionally is exactly the remaining mathematics.
-/
theorem openBridge_of_upper_tendsto_zero
    (eps : ℕ → ℝ)
    (hupper :
      ∀ N : ℕ,
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N ≤ eps N)
    (heps : Filter.Tendsto eps Filter.atTop (nhds 0)) :
    OpenBridge := by
  unfold OpenBridge MCore.RH.NB.NBHilbertData.DNToZero
  exact squeeze_zero
    (fun N =>
      MCore.RH.R0.concreteNBData.DN_nonneg
        MCore.RH.R0.concreteGeneratorFamily N)
    hupper
    heps

/--
A complete analytic closing certificate for the internal R2 frontier.

The certificate deliberately says only what is mathematically necessary:
there exists an explicit real majorant for the concrete finite defects, valid
for every N, and that majorant tends to zero.  No particular rate such as
C/log N is baked into the definition.
-/
def VanishingUpperCertificate : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ N : ℕ,
      MCore.RH.R0.concreteNBData.DN
        MCore.RH.R0.concreteGeneratorFamily N ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0)

/--
Backward-dense compression of the remaining internal mathematics:
producing any vanishing upper certificate is equivalent to the open bridge
itself.

The reverse direction uses DN as its own certificate, so this theorem does not
smuggle in an estimate; it identifies exactly the shape a successful analytic
attack must supply.
-/
theorem vanishingUpperCertificate_iff_openBridge :
    VanishingUpperCertificate ↔ OpenBridge := by
  constructor
  · rintro ⟨eps, hupper, heps⟩
    exact openBridge_of_upper_tendsto_zero eps hupper heps
  · intro hopen
    refine ⟨
      fun N =>
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N,
      ?_,
      ?_⟩
    · intro N
      exact le_rfl
    · simpa [OpenBridge, MCore.RH.NB.NBHilbertData.DNToZero] using hopen

/--
Conditional composition to the actual repository endpoint.  The only external
ingredient remains the explicit R1 equivalence hypothesis.
-/
theorem vanishingUpperCertificate_iff_finalStatement_of_r1
    (hR1 : R1ExternalBridge) :
    VanishingUpperCertificate ↔ FinalStatement := by
  exact
    vanishingUpperCertificate_iff_openBridge.trans
      (openBridge_iff_finalStatement_of_r1 hR1)

/--
An asymptotically exact closing certificate: eventual domination is enough.
Finite prefixes do not affect a Tendsto-atTop statement.
-/
def EventuallyVanishingUpperCertificate : Prop :=
  ∃ eps : ℕ → ℝ,
    (∀ᶠ N : ℕ in Filter.atTop,
      MCore.RH.R0.concreteNBData.DN
        MCore.RH.R0.concreteGeneratorFamily N ≤ eps N) ∧
    Filter.Tendsto eps Filter.atTop (nhds 0)

theorem eventuallyVanishingUpperCertificate_iff_openBridge :
    EventuallyVanishingUpperCertificate ↔ OpenBridge := by
  constructor
  · rintro ⟨eps, hupper, heps⟩
    unfold OpenBridge MCore.RH.NB.NBHilbertData.DNToZero
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun N =>
        MCore.RH.R0.concreteNBData.DN_nonneg
          MCore.RH.R0.concreteGeneratorFamily N)
      hupper
      heps
  · intro hopen
    refine ⟨
      fun N =>
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N,
      Filter.Eventually.of_forall fun _ => le_rfl,
      ?_⟩
    simpa [OpenBridge, MCore.RH.NB.NBHilbertData.DNToZero] using hopen

theorem eventuallyVanishingUpperCertificate_iff_finalStatement_of_r1
    (hR1 : R1ExternalBridge) :
    EventuallyVanishingUpperCertificate ↔ FinalStatement := by
  exact
    eventuallyVanishingUpperCertificate_iff_openBridge.trans
      (openBridge_iff_finalStatement_of_r1 hR1)

/--
Concrete logarithmic-rate certificate suggested by the finite R2 diagnostics.

The +2 shift keeps the logarithm strictly positive from N=0 onward and is
asymptotically irrelevant. DN is the frozen squared residual, not dN.
-/
def CLogUpperCertificate (C : ℝ) : Prop :=
  ∀ N : ℕ,
    MCore.RH.R0.concreteNBData.DN
      MCore.RH.R0.concreteGeneratorFamily N ≤
      C / Real.log ((N : ℝ) + 2)

/--
For every real constant C, the candidate majorant C/log(N+2) tends to zero.
-/
theorem C_div_log_nat_add_two_tendsto_zero (C : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => C / Real.log ((N : ℝ) + 2))
      Filter.atTop
      (nhds 0) := by
  refine tendsto_const_nhds.div_atTop ?_
  have hNatPlusTwo :
      Filter.Tendsto
        (fun N : ℕ => (N : ℝ) + 2)
        Filter.atTop
        Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    obtain ⟨n : ℕ, hn⟩ := exists_nat_ge (b - 2)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    have hcast : (n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast hm
    linarith
  exact Real.tendsto_log_atTop.comp hNatPlusTwo

/--
The asymptotic C/log(N+2) certificate: the bound only needs to hold eventually.
-/
def EventuallyCLogUpperCertificate (C : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop,
    MCore.RH.R0.concreteNBData.DN
      MCore.RH.R0.concreteGeneratorFamily N ≤
      C / Real.log ((N : ℝ) + 2)

theorem openBridge_of_eventuallyCLogUpperCertificate
    (C : ℝ)
    (hC : EventuallyCLogUpperCertificate C) :
    OpenBridge := by
  apply eventuallyVanishingUpperCertificate_iff_openBridge.mp
  exact
    ⟨fun N => C / Real.log ((N : ℝ) + 2),
      hC,
      C_div_log_nat_add_two_tendsto_zero C⟩

/--
A global C/log(N+2) upper bound is sufficient to close the internal R2 bridge.
-/
theorem vanishingUpperCertificate_of_CLogUpperCertificate
    (C : ℝ)
    (hC : CLogUpperCertificate C) :
    VanishingUpperCertificate := by
  exact
    ⟨fun N => C / Real.log ((N : ℝ) + 2),
      hC,
      C_div_log_nat_add_two_tendsto_zero C⟩

theorem openBridge_of_CLogUpperCertificate
    (C : ℝ)
    (hC : CLogUpperCertificate C) :
    OpenBridge := by
  exact
    vanishingUpperCertificate_iff_openBridge.mp
      (vanishingUpperCertificate_of_CLogUpperCertificate C hC)

/--
The internal falsity endpoint: the certified nonnegative DN limit is strictly
positive. This is a definition only; no claim that it holds is made.
-/
def FalseEndpoint : Prop :=
  0 <
    MCore.RH.R0.concreteNBData.DNLimit
      MCore.RH.R0.concreteGeneratorFamily

/--
Because the frozen DN limit is nonnegative, failure of the compressed zero
endpoint is exactly strict positivity of that limit.
-/
theorem not_compressedEndpoint_iff_falseEndpoint :
    (¬ CompressedEndpoint) ↔ FalseEndpoint := by
  unfold CompressedEndpoint FalseEndpoint
  constructor
  · intro hne
    exact lt_of_le_of_ne
      (MCore.RH.R0.concreteNBData.DNLimit_nonneg
        MCore.RH.R0.concreteGeneratorFamily)
      (Ne.symm hne)
  · intro hpos hzero
    exact (ne_of_gt hpos) hzero

/--
The true and false internal endpoints are exact complements.
-/
theorem falseEndpoint_iff_not_openBridge :
    FalseEndpoint ↔ ¬ OpenBridge := by
  constructor
  · intro hfalse hopen
    exact (not_compressedEndpoint_iff_falseEndpoint.mpr hfalse)
      (openBridge_iff_compressedEndpoint.mp hopen)
  · intro hnot
    apply not_compressedEndpoint_iff_falseEndpoint.mp
    intro hcompressed
    exact hnot (openBridge_iff_compressedEndpoint.mpr hcompressed)

/--
The false endpoint is exactly the nonexistence of any vanishing upper
certificate.  This is the formal falsification contract for every proposed
analytic bound.
-/
theorem falseEndpoint_iff_noVanishingUpperCertificate :
    FalseEndpoint ↔ ¬ VanishingUpperCertificate := by
  exact
    falseEndpoint_iff_not_openBridge.trans
      (not_congr vanishingUpperCertificate_iff_openBridge).symm

/--
If the false endpoint held, every proposed majorant tending to zero would fail
at some finite index.  This gives a concrete counterexample obligation for any
candidate BCF/Vasyunin upper bound.
-/
theorem falseEndpoint_witnesses_majorant_failure
    (hfalse : FalseEndpoint)
    (eps : ℕ → ℝ)
    (heps : Filter.Tendsto eps Filter.atTop (nhds 0)) :
    ∃ N : ℕ,
      eps N <
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N := by
  by_contra hno
  have hupper :
      ∀ N : ℕ,
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N ≤ eps N := by
    intro N
    by_contra hle
    exact hno ⟨N, lt_of_not_ge hle⟩
  exact
    (falseEndpoint_iff_not_openBridge.mp hfalse)
      (openBridge_of_upper_tendsto_zero eps hupper heps)

/--
On the false lane, every fixed C/log(N+2) proposal has a finite counterexample
index.
-/
theorem falseEndpoint_witnesses_CLog_failure
    (hfalse : FalseEndpoint)
    (C : ℝ) :
    ∃ N : ℕ,
      C / Real.log ((N : ℝ) + 2) <
        MCore.RH.R0.concreteNBData.DN
          MCore.RH.R0.concreteGeneratorFamily N := by
  exact
    falseEndpoint_witnesses_majorant_failure
      hfalse
      (fun N => C / Real.log ((N : ℝ) + 2))
      (C_div_log_nat_add_two_tendsto_zero C)

/--
Conditional false-lane composition through the explicit R1 external
interface. Again, R1 is a theorem hypothesis, not a project axiom.
-/
theorem falseEndpoint_iff_not_finalStatement_of_r1
    (hR1 : R1ExternalBridge) :
    FalseEndpoint ↔ ¬ FinalStatement := by
  exact not_compressedEndpoint_iff_falseEndpoint.symm.trans (not_congr hR1)

/--
Research status proposition: the unresolved internal mathematical content is
OpenBridge. The BCF combined-block estimate is a proposed analytic route to
this proposition, not an assumption inserted here.
-/
def MaterialFrontier : Prop := OpenBridge

theorem materialFrontier_iff_openBridge :
    MaterialFrontier ↔ OpenBridge := by
  rfl

#print axioms MCore.RH.R2.openBridge_iff_compressedEndpoint
#print axioms MCore.RH.R2.openBridge_iff_finalStatement_of_r1
#print axioms MCore.RH.R2.openBridge_of_upper_tendsto_zero
#print axioms MCore.RH.R2.vanishingUpperCertificate_iff_openBridge
#print axioms MCore.RH.R2.vanishingUpperCertificate_iff_finalStatement_of_r1
#print axioms MCore.RH.R2.eventuallyVanishingUpperCertificate_iff_openBridge
#print axioms MCore.RH.R2.eventuallyVanishingUpperCertificate_iff_finalStatement_of_r1
#print axioms MCore.RH.R2.C_div_log_nat_add_two_tendsto_zero
#print axioms MCore.RH.R2.vanishingUpperCertificate_of_CLogUpperCertificate
#print axioms MCore.RH.R2.openBridge_of_CLogUpperCertificate
#print axioms MCore.RH.R2.openBridge_of_eventuallyCLogUpperCertificate
#print axioms MCore.RH.R2.not_compressedEndpoint_iff_falseEndpoint
#print axioms MCore.RH.R2.falseEndpoint_iff_not_openBridge
#print axioms MCore.RH.R2.falseEndpoint_iff_noVanishingUpperCertificate
#print axioms MCore.RH.R2.falseEndpoint_witnesses_majorant_failure
#print axioms MCore.RH.R2.falseEndpoint_witnesses_CLog_failure
#print axioms MCore.RH.R2.falseEndpoint_iff_not_finalStatement_of_r1
#print axioms MCore.RH.R2.materialFrontier_iff_openBridge

end
end MCore.RH.R2
