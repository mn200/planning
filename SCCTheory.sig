signature SCCTheory =
sig
  type thm = Thm.thm

  (*  Definitions  *)
    val SCC_def : thm
    val lift_def : thm

  (*  Theorems  *)
    val scc_disjoint_lemma : thm
    val scc_tc_inclusion : thm

  val SCC_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [list] Parent theory of "SCC"

   [SCC_def]  Definition

      |- ∀R vs.
           SCC R vs ⇔
           (∀v v'. v ∈ vs ∧ v' ∈ vs ⇒ R⁺ v v' ∧ R⁺ v' v) ∧
           (∀v v'. v ∈ vs ∧ v' ∉ vs ⇒ ¬R⁺ v v' ∨ ¬R⁺ v' v) ∧ vs ≠ ∅

   [lift_def]  Definition

      |- ∀R vs vs'. lift R vs vs' ⇔ ∃v v'. v ∈ vs ∧ v' ∈ vs' ⇒ R v v'

   [scc_disjoint_lemma]  Theorem

      |- ∀R vs vs'. SCC R vs ∧ SCC R vs' ∧ vs ≠ vs' ⇒ DISJOINT vs vs'

   [scc_tc_inclusion]  Theorem

      [oracles: cheat] [axioms: ] []
      |- ∀R vs v v'.
           v ∈ vs ∧ v' ∈ vs ∧ SCC R vs ⇒
           (λv v'. R v v' ∧ v ∈ vs ∧ v' ∈ vs)⁺ v v'


*)
end
