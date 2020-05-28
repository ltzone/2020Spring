Require Import VST.floyd.proofauto.
Require Import EV.AuxiliaryTac.
Require Export VST.floyd.Funspec_old_Notation.
Require EV.max3 EV.swap EV.tri EV.gcd EV.append.

Local Open Scope logic.

(* ################################################################# *)
(** * Task 1: The Max of Three *)

Module Verif_max3.

Import EV.max3.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [max3]:

      int max3(int x, int y, int z)
      {
        if (x < y)
          if (y < z)
            return z;
          else
            return y;
        else
          if (x < z)
            return z;
          else
            return x;
      }

    Specification:
*)

Definition max3_spec :=
 DECLARE _max3
  WITH x: Z, y: Z, z: Z
  PRE  [ _x OF tint, _y OF tint, _z OF tint ]
     PROP  (Int.min_signed <= x <= Int.max_signed;
            Int.min_signed <= y <= Int.max_signed;
            Int.min_signed <= z <= Int.max_signed)
     LOCAL (temp _x (Vint (Int.repr x));
            temp _y (Vint (Int.repr y));
            temp _z (Vint (Int.repr z)))
     SEP   ()
  POST [ tint ]
    EX r: Z, 
     PROP  (r = x \/ r = y \/ r = z;
            r >= x;
            r >= y;
            r >= z)
     LOCAL (temp ret_temp (Vint (Int.repr r)))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ max3_spec ]).

Lemma body_max3: semax_body Vprog Gprog f_max3 max3_spec.
Proof.
  start_function.
  (* FILL IN HERE *) Admitted.

End Verif_max3.
(** [] *)

(* ################################################################# *)
(** * Task 2: Swap by Arith *)

Module Verif_swap.

Import EV.swap.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [uint_swap_arith]:

      void uint_swap_arith (unsigned int * px, unsigned int * py) {
        * px = * px + * py;
        * py = * px - * py;
        * px = * px - * py;
      }

    Specification:
*)

Definition uint_swap_arith_spec :=
 DECLARE _uint_swap_arith
  WITH x: Z, y: Z, px: val, py: val
  PRE  [ _px OF (tptr tuint), _py OF (tptr tuint) ]
     PROP  ()
     LOCAL (temp _px px; temp _py py)
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) px;
            data_at Tsh tuint (Vint (Int.repr y)) py)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (data_at Tsh tuint (Vint (Int.repr x)) py;
            data_at Tsh tuint (Vint (Int.repr y)) px).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ uint_swap_arith_spec ]).

Lemma body_uint_swap_arith: semax_body Vprog Gprog
                              f_uint_swap_arith uint_swap_arith_spec.
Proof.
  start_function.
  (* FILL IN HERE *) Admitted.

End Verif_swap.
(** [] *)

(* ################################################################# *)
(** * Task 3: Tri *)

Module Verif_tri.

Import EV.tri.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C program:

      unsigned int tri_for (int n) {
        unsigned int s;
        int i;
        s = 0;
        for (i = 0; i < n; ++ i)
          s = s + i;
        return s;
      }

      unsigned int tri_while (int n) {
        unsigned int s;
        s = 0;
        while (n > 0) {
          n = n - 1;
          s = s + n;
        }
        return s;
      }

    Specification:
*)

Definition tri_spec (_tri_name: ident) :=
 DECLARE _tri_name
  WITH n: Z
  PRE  [ _n OF tint ]
     PROP  (0 <= n <=Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n)))
     SEP   ()
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (n * (n-1)/2))))
     SEP   ().

Definition Gprog : funspecs :=
  ltac:(with_library prog [ tri_spec _tri_for; tri_spec _tri_while ]).

(** Hint: in your proof, lemma [Z_div_plus_full] and tactic [ring] might be
    helpful. (Ring is just a fancier version of omega which can also handle
    multiplication. *)
Lemma body_tri_for: semax_body Vprog Gprog
                            f_tri_for (tri_spec _tri_for).
Proof.
  start_function.
  (* FILL IN HERE *) Admitted.

Lemma body_tri_while: semax_body Vprog Gprog
                            f_tri_while (tri_spec _tri_while).
Proof.
  start_function.
  (* FILL IN HERE *) Admitted.

End Verif_tri.
(** [] *)

(* ################################################################# *)
(** * Task 4: Greatst Common Divisor *)

Module Verif_gcd.

Import EV.gcd.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** C function [gcd]:

      int gcd(int n, int m) {
        int r = m % n;
        if (r == 0)
          return n;
        else
          return gcd(r, n);
      }

    This function calculates the greatest common divisor of two integers.
    [Z.gcd] is defined as part of Coq's standard library. Using this definition,
    we can write specification as follows:
*)

Definition gcd_spec :=
 DECLARE _gcd
  WITH n: Z, m: Z
  PRE  [ _n OF tint, _m OF tint ]
     PROP  (0 < n <= Int.max_signed;
            0 <= m <= Int.max_signed)
     LOCAL (temp _n (Vint (Int.repr n));
            temp _m (Vint (Int.repr m)))
     SEP   ()
  POST [ tint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.gcd n m))))
     SEP   ().

Definition Gprog : funspecs := ltac:(with_library prog [ gcd_spec ]).

(** We first provide three useful lemmas. You may use it in your proofs. *)

Lemma aux1: forall n, 0 < n <= Int.max_signed -> Int.repr n <> Int.zero.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + omega.
  + rep_omega.
    (* This VST tactic is used to handle linear programming with 32-bit bounds.
       You can use it in your own proofs. *)
  + rep_omega.
Qed.

Lemma aux2: forall m, 0 <= m <= Int.max_signed -> Int.repr m <> Int.repr Int.min_signed.
Proof.
  intros.
  intro.
  apply repr_inj_signed in H0.
  + rep_omega.
    (* [rep_omega] can also solve normal linear proof goals. The proof goal
       does not need to be [repable_signed]. *)
  + rep_omega.
  + rep_omega.
Qed.

Lemma mods_repr: forall n m,
  Int.min_signed <= n <= Int.max_signed ->
  Int.min_signed <= m <= Int.max_signed ->
  Int.mods (Int.repr m) (Int.repr n) = Int.repr (Z.rem m n).
(* Here [Z.rem] is the remainder of [m divides n]. *)
Proof.
  intros.
  unfold Int.mods.
  rewrite Int.signed_repr by rep_omega.
  rewrite Int.signed_repr by rep_omega.
  reflexivity.
Qed.

(** Now, fill in the holes in the following proof. *)
Lemma body_gcd: semax_body Vprog Gprog f_gcd gcd_spec.
Proof.
  start_function.
  forward.
  {
    (* Hint: remember that you can use [aux1] and [aux2]. *)
    (* FILL IN HERE *) admit.
  }
  rewrite mods_repr by rep_omega.
  forward_if.
  {
    (* Hint: you can always use [Search] to find useful theorems in Coq's
       standard library and VST's library. For example, [Z.gcd_rem] may be
       useful. *)
    (* FILL IN HERE *) admit.
  }
  {
    assert (Z.rem m n <> 0).
    {
      unfold not; intro.
      rewrite H2 in H1.
      apply H1; reflexivity.
    }
    forward_call (Z.rem m n, n).
    {
      (* FILL IN HERE *) admit.
    }
    (* FILL IN HERE *) admit.
  }
(* Change it to "Qed." *) Admitted.

End Verif_gcd.

Module List_seg.

(* ################################################################# *)
(** * Task 5. List Segments *)

Import EV.append.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** In this part, we will verify two C functions:

      struct list {
        unsigned int head;
        struct list * tail;
      };

      unsigned sumlist (struct list *p) {
        unsigned s = 0;
        struct list * t = p;
        unsigned h;
        while (t) {
           h = t->head;
           t = t->tail;
           s = s + h;
        }
        return s;
      }

      struct list *append (struct list *x, struct list *y) {
        struct list *t, *u;
        if (x==NULL)
          return y;
        else {
          t = x;
          u = t->tail;
          while (u!=NULL) {
            t = u;
            u = t->tail;
          }
          t->tail = y;
          return x;
        }
      }

    Using [listrep], we can state their specification.
*)

Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

Definition sum_int (sigma: list Z): Z :=
  fold_right Z.add 0 sigma.

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sigma : list Z, p: val
  PRE [ _p OF (tptr t_struct_list) ]
     PROP  ()
     LOCAL (temp _p p)
     SEP   (listrep sigma p)
  POST [ tuint ]
     PROP  ()
     LOCAL (temp ret_temp (Vint (Int.repr (sum_int sigma))))
     SEP   (listrep sigma p).

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep (s1++s2) r).

(** Both C functions traverse a linked list using a while loop. Thus, the
    keypoint of verifying them is to write down the correct loop invariant.
    The following diagram demonstrates an intermediate state in traversing.

        +---+---+            +---+---+   +---+---+   +---+---+   
  x ==> |   |  ===> ... ===> |   | y ==> |   | z ==> |   |  ===> ... 
        +---+---+            +---+---+   +---+---+   +---+---+

      | <==== Part 1 of sigma =====> |            | <== Part 2 ==> |

      | <========================== sigma =======================> |

    To properly describe loop invariants, we need a predicate to describe
    the partial linked list from address [x] to address [y]. We provide its
    definition for you. But it is your task to prove its important properties.
*)

Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.

Arguments lseg sigma x y : simpl never.

Lemma singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x |-- lseg [a] x y.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** In the next lemma, try to understand how to use [sep_apply]. *)
Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval |-- listrep sigma x.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    (** The following tactic "apply" [IHsigma] on the left side of derivation. *)
    sep_apply (IHsigma u).
    entailer!.
Qed.

Lemma lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

Lemma lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** Try to use prove the following assertion derivation use the lemmas above.
    The first step is done for you. *)
Example lseg_ex: forall s1 s2 s3 x y z,
  lseg s1 x y * lseg s2 y z * lseg s3 z nullval |-- listrep (s1 ++ s2 ++ s3) x.
Proof.
  intros.
  sep_apply (lseg_lseg s2 s3 y z nullval).
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Task 6. Sum of a List *)

(** Now, you are going to prove [sumlist] correct. The following lemmas are
    copied from [verif_reverse2] for proof automation. *)

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
intros.
revert p; induction sigma; 
  unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
 destruct sigma; unfold listrep; fold listrep;
 intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto.
 simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Module sumlist.

(** Another auxiliary lemma. Hint: use [Search] when you need to find a
    lemma. *)
Lemma sum_int_snoc:
  forall a b, sum_int (a++b :: nil) = (sum_int a) + b.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

Definition Gprog : funspecs :=
  ltac:(with_library prog [ sumlist_spec ]).

(** Hint: take a look at Verif_reverse and learn its proof strategy. *)
Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End sumlist.

(* ################################################################# *)
(** * Task 7: Append *)

Module append.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append_spec ]).

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End append.

(* ################################################################# *)
(** * Task 8: List box segments *)

(** Now, consider this alternative implementation of append:

      void append2(struct list * * x, struct list * y) {
        struct list * h;
        h = * x;
        while (h != NULL) {
          x = & (h -> tail);
          h = * x;
        }
        * x = y;
      }

    You should prove:
*)

Module append2.

Definition append2_spec :=
 DECLARE _append2
  WITH x: val, y: val, s1: list Z, s2: list Z, p :val
  PRE [ _x OF (tptr (tptr t_struct_list)) , _y OF (tptr t_struct_list)]
     PROP()
     LOCAL (temp _x x; temp _y y)
     SEP (data_at Tsh (tptr t_struct_list) p x;
          listrep s1 p;
          listrep s2 y)
  POST [ tvoid ]
     EX q: val,
     PROP()
     LOCAL()
     SEP (data_at Tsh (tptr t_struct_list) q x;
          listrep (s1 ++ s2) q).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append2_spec ]).

(** You may find it inconvenient to complete this proof directly using [listrep]
    and [lseg]. You may need another predicate for [list box segment].

         +---+---+            +---+---+   +---+---+   +---+---+   
   p ==> |   |  ===> ... ===> |   |   ==> |   |   ==> |   |  ===> ... 
         +---+---+            +---+---+   +---+---+   +---+---+

       | <====            list segment      =====> |

 | <====           list box segment     =====> |

    Try to define this predicate by yourself and prove [lbseg_lseg].
*)


Fixpoint lbseg (sigma: list Z) (x y: val) : mpred.
(* FILL IN HERE *) Admitted.
(** [] *)

Lemma lbseg_lseg: forall s3 x y z,
  lbseg s3 x y * data_at Tsh (tptr t_struct_list) z y |--
  EX y', data_at Tsh (tptr t_struct_list) y' x*lseg s3 y' z.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** Hint: adding more lemmas for [lbseg] may be useful. *)
Lemma body_append2: semax_body Vprog Gprog f_append2 append2_spec.
(* FILL IN HERE *) Admitted.
(** [] *)

End append2.

End List_seg.
