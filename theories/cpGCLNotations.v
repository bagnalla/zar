(** * cpGCL notation declarations. *)

From zar Require Import cpGCL.

Delimit Scope cpGCL_scope with cpGCL.

Notation "'skip'" :=
  CSkip (at level 0) : cpGCL_scope.
Notation "'abort'" :=
  CAbort (at level 0) : cpGCL_scope.
Notation "x <-- e" :=
  (CAssign x e)
    (at level 0, e at level 85, no associativity) : cpGCL_scope.
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 90, right associativity) : cpGCL_scope.
Notation "'if' e 'then' c1 'else' c2 'end'" :=
  (CIte e c1 c2) (at level 89, e at level 99,
      c1 at level 99, c2 at level 99) : cpGCL_scope.
Notation "'while' e 'do' c 'end'" :=
  (CWhile e c) (at level 89, e at level 99, c at level 99) : cpGCL_scope.
Notation "'obs' e" :=
  (CObserve e) (at level 0, e at level 85, no associativity) : cpGCL_scope.
