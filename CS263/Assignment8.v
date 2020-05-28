(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2020/05/15.                                             *)
(* Due: 2020/05/19, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment8.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment8.vo" file is generated.         *)
(*                                                                   *)
(* 5. Do not copy and paste others' answer.                          *)
(*                                                                   *)
(* 6. Using any theorems and/or tactics provided by Coq's standard   *)
(*    library is allowed in this assignment, if not specified.       *)
(*                                                                   *)
(* 7. When you finish, answer the following question:                *)
(*                                                                   *)
(*      Who did you discuss with when finishing this                 *)
(*      assignment? Your answer to this question will                *)
(*      NOT affect your grade.                                       *)
(*      (* FILL IN YOUR ANSWER HERE AS COMMENT *)                    *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.ZArith.ZArith.

(* ################################################################# *)
(** * Task 1: Understanding VST *)

Module Task1.

(** **** Exercise: 1 star, standard  *)

(** In our tutorial, we cannot prove that the following C program satisfying
    the Hoare triple below.

      int add(int x, int y) {
        int z;
        z = x + y;
        return z;
      }

      Definition add_spec :=
       DECLARE _add
        WITH x: Z, y: Z
        PRE  [ _x OF tint, _y OF tint ]
           PROP  ()
           LOCAL (temp _x (Vint (Int.repr x)); temp _y (Vint (Int.repr y)))
           SEP   ()
        POST [ tint ]
           PROP  ()
           LOCAL (temp ret_temp (Vint (Int.repr (x + y))))
           SEP   ().

      The reason is that overflow in signed integer arithmetic is undefined
      behavior in C and the precondition does not exclude that possibility.

      Is the explanation above correct? 1. Yes. 2. No. *)

Definition my_choice1: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** In VST, [forward] is a powerful command for forward symbolic execution. For
    example, the following is to one proof goal before [forward] and the
    corresponding proof goal after [forward].

    [

     semax Delta
       (PROP  ( )
        LOCAL (temp _w w;
               temp _v v)
        SEP   (listrep s1 w;
               data_at Tsh t_struct_list (Vint (Int.repr s2a), y) v;
               listrep s2b y))
       (_t = (_v -> _tail);
        MORE_COMMANDS)
     POSTCONDITION

    ]

    [

     semax Delta
       (PROP  ( )
        LOCAL (temp _t y;
               temp _w w;
               temp _v v)
        SEP   (listrep s1 w;
               data_at Tsh t_struct_list (Vint (Int.repr s2a), y) v;
               listrep s2b y))
       ((_v -> _tail) = _w;
        MORE_COMMANDS)
       POSTCONDITION

    ]

    The [forward] tactic actually builds a Hoare logic proof tree for the former
    triple from a proof tree for the latter triple. In this proof, it uses
    VST's consequence rule and some other Hoare logic proof rules.

    Which of the following proof rules are needed?
    1. The assgnment rule.
    2. The sequence rule.
    3. The assgnment rule and the sequence rule. *)

Definition my_choice2: Z := 3.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following statement correct? 1. Yes. 2. No.

    In VST, we can prove the following assertion derivation:

       forall p v, data_at Tsh tint v p |--
                   data_at Tsh tint v p * data_at Tsh tint v p  *)

Definition my_choice3: Z := 2.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Understanding Control Flows *)

(** In this task, we consider the programming language in our lecture about
    control flows. In other words, there is no run time error. *)

Module Task2.

(** **** Exercise: 1 star, standard  *)

(** Can we prove the following Hoare triple, using the Hoare logic for control
    flow programs? Suppose the logic for assertion derivation is sound and
    complete. 1. Yes. 2. No.

       {{ {[ X ]} = n }}
          X ::= X - 1
       {{ {[ X ]} = n - 1 }}
       {{ False }}
       {{ {[ X ]} = n - 1 }}
*)

Definition my_choice1: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    [
       {{ P }}
          If b Then (c ;; While b Do c EndWhile) Else Skip EndIf
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ]
    if and only if
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ].
    
    1. Yes. 2. No.
*)
(* c in the first statement may produce BREAK/CONTINUE post conditions stronger then False *)
Definition my_choice2: Z := 2.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ]
    if and only if
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ False }}
       {{ False }}
    ]
    
    
    1. Yes. 2. No.
*)
(* While must exit as Normal, therefore the other two conditions will make no difference *)
Definition my_choice3: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    For any [st], [ek] and [st'],
    [[
       ceval (While b Do c EndWhile) st ek st'
    ]]
    if and only if
    [[
       ceval (While (0 == 0) Do If b Then c Else Break EndIf EndWhile) st ek st'
    ]]
    
    1. Yes. 2. No.
*)


(*
  Note that While must exit as normal kind.
  
  (/\' ~ seq_sem, /\ ~ normal seq)
  
  ceval (While b Do c EndWhile) st ek st'
  -> exists n, ((test b) /\' c )*n_times /\' (test ~b) st ek st'
  
  
  ceval (While (0 == 0) Do If b Then c Else Break EndIf EndWhile) st ek st'
  -> exists n, ((test 0==0) /\' (If b Then c Else Break))*n_times /\' (test !0==0) st ek st'
  # test 0 == 0 is always true and normal,
    and that ek_Break will be rechecked by (test b)
  -> exists n, ((test b) /\ c || (test ~b) /\ Break)*n_times /\' (test !0==0)
  
  For equivalence,
  -> let n_2 = n_1 + 1
  <- let n_1 = n_2 - 1 and that n_2 can't be zero.
*)

Definition my_choice4: Z := 1.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    For any [st], [c'], [s'], [st'],
    [[
       clos_refl_trans cstep
         (While b Do c EndWhile, nil, st)
         (c', s', st')
    ]]
    if and only if
    [[
       clos_refl_trans cstep
         (While (0 == 0) Do If b Then c Else Break EndIf EndWhile, nil, st)
         (c', s', st')
    ]]
    Here, we use the small step semantics with control stack.

    1. Yes. 2. No.
*)

(*
   (While b Do c EndWhile, nil, st)
   --> (If b Then c Else Break, [b,c,Skip], st)
   
   (While (0 == 0) Do If b Then c Else Break EndIf EndWhile, nil, st)
   --> (If (0==0) Then (If b Then c Else Break EndIf) Else Break,
        [0==0, (If ...) , Skip], st)
   (0==0) in the second statement will never appear in the evaluation of statement 1
*)

Definition my_choice5: Z := 2.
(** [] *)

End Task2.

(* Fri May 15 23:56:59 CST 2020 *)
