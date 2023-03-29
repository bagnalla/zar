(** * Tutorial. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lra.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  compile cotree cocwp cpGCL cpo cwp equidistribution eR misc itree order tactics tree.
Local Open Scope cpGCL_scope.

(** Import pre-defined cpGCL definitions and helpers. *)
Require Import prelude.

(** Your cpGCL program. *)
Definition prog (out : string) : cpGCL :=
  CUniform (const 10%nat) (fun m => out <-- m).

Lemma wf_prog (out : string) :
  wf_cpGCL (prog out).
Proof.
Admitted.

Section prog_equidistribution.
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).
  Context (out : string).
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree (prog out) empty).

  Theorem prog_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp (prog out) (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_prog; auto.
  Qed.
End prog_equidistribution.

(** Extracting the sampler. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE Z :=
  ITree.map (fun s => as_int (s "out")) (cpGCL_to_itree (prog "out") empty).
Extraction "extract/tutorial/prog.ml" sampler.
