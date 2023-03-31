(** * Tutorial/template. *)

Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import Streams Basics QArith String Lia Lqa.
Local Open Scope program_scope.
Local Open Scope string_scope.

From ITree Require Import
  ITree ITreeFacts.
Import ITreeNotations.
Local Open Scope itree_scope.

From zar Require Import
  compile cpGCL cpo cwp equidistribution eR itree misc tactics.
Local Open Scope cpGCL_scope.

(** Import pre-defined cpGCL definitions and helpers. *)
Require Import prelude.

(** We begin with a cpGCL program to be compiled (see cpGCL.v for
    syntax). For example, the following program implements a binomial
    posterior with p=1/2 over variable n. Note that cpGCL values are
    not typed (for now), so we must sometimes coerce values to the
    intended types using functions like 'as_bool' and 'as_int' (also
    defined in cpGCL.v). *)
Definition prog : cpGCL :=
  flip "b" (1#2) ;
  "n" <-- 0%Z;
  while (fun s => as_bool (s "b")) do
    "n" <-- (fun s => Z.succ (as_int (s "n"))) ;
    flip "b" (1#2)
  end.

(** Prove well-formedness of the program so that the equidistribution
    theorem can be applied.*)
Lemma wf_prog :
  wf_cpGCL prog.
Proof. repeat constructor; unfold const; lra. Qed.

(** Here we instantiate the equidistribution theorem with the program. *)
Section prog_equidistribution.
  
  (** We parameterize over a sampling environment - a record
      containing a sequence of bitstreams and a proof that they are
      uniformly distributed (see the definition in
      equidistribution.v). We also parameterize over a predicate P
      over program states and a sequence of terminal program states. *)
  Context (env : SamplingEnvironment) (P : St -> bool) (samples : nat -> St).

  (** Suppose that each sample is the result of feeding the
      corresponding bitstream from the sampling environment through
      the itree compiled from the program (using the empty state). *)
  Hypothesis bitstreams_samples :
    forall i, iproduces (eq (samples i)) (env.(bitstreams) i)
           (cpGCL_to_itree prog empty).

  (** Then, the relative frequency of samples satisfying P (wrt. the
      total number of samples) converges in the limit to the
      conditional weakest pre-expectation of [fun s => if P s then 1 else
      0] (i.e., the probability of P). *)
  Theorem prog_samples_equidistributed :
    converges (freq (is_true ∘ P) ∘ prefix samples)
      (cwp prog (fun s => if P s then 1 else 0) empty).
  Proof.
    eapply cpGCL_samples_equidistributed; eauto; apply wf_prog; auto.
  Qed.
End prog_equidistribution.

(** Compile and extract itree sampler from the program to the
    /extract/tutorial directory. We project out variable n from the
    program state (via ITree.map) to yield a sampler with return type Z. *)
From Coq Require Import ExtrOcamlBasic ExtrOcamlString.
Definition sampler : itree boolE Z :=
  ITree.map (fun s => as_int (s "n")) (cpGCL_to_itree prog empty).
Extraction "extract/tutorial/prog.ml" sampler.

(** Continue to /extract/tutorial/README.md for instructions on how to
    generate and perform empirical analysis on samples from the
    extracted itree sampler. *)
