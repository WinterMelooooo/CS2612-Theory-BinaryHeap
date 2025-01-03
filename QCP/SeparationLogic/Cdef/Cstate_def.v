Require Import Coq.Classes.Morphisms.
Require Import AUXLib.Feq.

From SimpleC.ASRT Require Import DefFiles.
From SimpleC.CSE Require Import Cexpr_def.
From SimpleC.Common Require Import CTypes.
From SimpleC.Common Require Import COps.
From SimpleC.CoreLang Require Import CTypes.
From SimpleC.SL Require Mem.

From AUXLib Require Import Axioms List_lemma.
From compcert.lib Require Import Coqlib Integers.



Inductive StateType : Type :=
| In_Global : StateType
| In_func_block (ret: list Prod_ret) (pf: AsrtProof)
| In_while_block (cond: ACexpr) (inv: Assertion) (pf: AsrtProof)
(* | In_do_block_first (ps : list partial_statement)
| In_do_block (inv: Assertion) (pf: AsrtProof) *)
| In_for_block (cond: ACexpr) (incr: ACsimplecommand) (inv: Assertion) (pf: AsrtProof)
| In_switch_block (cond: ACexpr) (Asrt: Assertion) (label_list: list Z)
| In_switch_cases_block (label: Z)
| In_switch_default_block
| In_if_then_block (else_pre: Assertion)
  (** records the pre-condition of else branch for later use *)
| In_if_else_block (then_post: Assertion)
  (** records the post-condition of then branch for later use *)
.
(**r Here need more information rather then only the state & state_ident before enter the block *)

Record State : Type := mk_State {
  Normal_ret : Assertion;
  Break_ret : Assertion;
  Continue_ret : Assertion;
  Return_ret : list Prod_ret;
}.

Record Env : Type := mk_env {
  Funcspecs : list funcspec;
  (* Funcpreds : list FuncDef_input; *)
  (* Seppreds : list SepDef_input; *)
  Machine_stack : list (StateType * State);
}.

Inductive val : Type :=
  | Vuint : int -> val
  | Vint : int -> val
  | Vlong : int64 -> val
  | Vulong : int64 -> val
  | Vchar : byte -> val
  | Vuchar : byte -> val
.

Definition type_of_val (v : val) : SimpleCtype :=
  match v with
    | Vuint _ => CT_basic (CT_int Unsigned I32)
    | Vint _ => CT_basic (CT_int Signed I32)
    | Vlong _ => CT_basic (CT_int Signed I64)
    | Vulong _ => CT_basic (CT_int Unsigned I64)
    | Vchar _ => CT_basic (CT_int Signed I8)
    | Vuchar _ => CT_basic (CT_int Unsigned I8)
  end.

Definition eqb_val (a b : val) : bool :=
  match a, b with
    | Vuint i , Vuint j => Int.eq i j
    | Vint i , Vint j => Int.eq i j
    | Vlong i , Vlong j => Int64.eq i j
    | Vulong i , Vulong j => Int64.eq i j
    | Vchar i , Vchar j => Byte.eq i j
    | Vuchar i , Vuchar j => Byte.eq i j
    | _ , _ => false
  end.


Notation VarsAddrType := (ident -> option (Mem.addr * SimpleCtype)).

Record prog_state : Type := mk_progstate {
  vars_addr : VarsAddrType;
  mem : Mem.mem;
}.

Definition empty_vars_addr : VarsAddrType := fun _ => None.

Definition vars_addr_empty (J : VarsAddrType) : Prop := forall i, J i = None.

Lemma empty_vars_addr_empty : vars_addr_empty empty_vars_addr.
Proof.
  unfold vars_addr_empty. intros. unfold empty_vars_addr. auto.
Qed.

Lemma vars_addr_empty_IS_empty_vars_addr : forall a, vars_addr_empty a -> f_eq a empty_vars_addr.
Proof.
  unfold vars_addr_empty, f_eq. intros. auto.
Qed.

Lemma vars_addr_empty_IS_empty_vars_addr' : forall a, vars_addr_empty a -> a = empty_vars_addr.
Proof.
  intros. apply fun_ext1. apply vars_addr_empty_IS_empty_vars_addr. auto.
Qed.

Definition vars_addr_join (J1 J2 J: VarsAddrType) : Prop :=
  forall i,
    (J1 i = None /\ J2 i = None /\ J i = None) \/
    (exists a1 t1, J1 i = Some (a1, t1) /\ J2 i = None /\ J i = Some (a1, t1)) \/
    (exists a2 t2, J1 i = None /\ J2 i = Some (a2, t2) /\ J i = Some (a2, t2)).

#[export] Instance vars_addr_join_congr :
  Proper (f_eq ==> f_eq ==> f_eq ==> iff) vars_addr_join.
Proof.
  unfold Proper, respectful, vars_addr_join, f_eq.
  intros. split ; intros ; specialize (H i); specialize (H0 i); specialize (H1 i); specialize (H2 i).
  - rewrite <- H. rewrite <- H0. rewrite <- H1. auto.
  - rewrite H. rewrite H0. rewrite H1. auto.
Qed.

Lemma vars_addr_join_comm : forall J1 J2 J,
  vars_addr_join J1 J2 J ->
  vars_addr_join J2 J1 J.
Proof.
  unfold vars_addr_join. intros.
  specialize (H i). destruct H as [H | [H | H]].
  - left. destruct H as [H1 [H2 H3]]. auto.
  - right. right. destruct H as [a1 [t1 [H1 [H2 H3]]]]. exists a1. exists t1. auto.
  - right. left. destruct H as [a2 [t2 [H1 [H2 H3]]]]. exists a2. exists t2. auto.
Qed.

Lemma vars_addr_join_empty1 : forall J, vars_addr_join empty_vars_addr J J.
Proof.
  intros. unfold vars_addr_join. intros.
  unfold empty_vars_addr.
  destruct (J i); auto.
  right. right. destruct p as [a t]. exists a. exists t. auto.
Qed.

Lemma vars_addr_join_empty2 : forall J, vars_addr_join J empty_vars_addr J.
Proof.
  intros. unfold vars_addr_join. intros.
  unfold empty_vars_addr.
  destruct (J i); auto.
  right. left. destruct p as [a t]. exists a. exists t. auto.
Qed.

Lemma vars_addr_join_emp_l: forall J J1, vars_addr_join empty_vars_addr J J1 -> J1 = J.
Proof.
  unfold vars_addr_join, empty_vars_addr; intros.
  apply fun_ext1. intros i.
  specialize (H i).
  destruct H as [ [H1 [H2 H3]] | [ [a1 [t1 [H1 [H2 H3]]]] | [a2 [t2 [H1 [H2 H3]]]] ] ].
  all: congruence.
Qed.

Lemma vars_addr_join_emp_r: forall J J1, vars_addr_join J empty_vars_addr J1 -> J1 = J.
Proof.
  intros. apply vars_addr_join_comm in H.
  apply vars_addr_join_emp_l in H. auto.
Qed.

Lemma vars_addr_join_assoc1: forall J1 J2 J3 J12 J123,
  vars_addr_join J1 J2 J12 ->
  vars_addr_join J12 J3 J123 ->
  exists J23,
  vars_addr_join J2 J3 J23 /\ vars_addr_join J1 J23 J123.
Proof.
  unfold vars_addr_join. intros J1 J2 J3 J12 J123 H1 H2.
  exists (fun i => match J2 i with
                    | None => J3 i
                    | Some (a2, t2) => Some (a2, t2)
                  end).
  split ; intros i; specialize (H1 i); specialize (H2 i).
  all: destruct H1 as [ [H1a [H1b H1c]] | [ [a1 [t1 [H1a [H1b H1c]]]] | [a2 [t2 [H1a [H1b H1c]]]] ] ];
       destruct H2 as [ [H2a [H2b H2c]] | [ [a12 [t12 [H2a [H2b H2c]]]] | [a3 [t3 [H2a [H2b H2c]]]] ] ];
       try congruence.
  - left. repeat split; auto. rewrite H1b. auto.
  - right. right. exists a3. exists t3. repeat split; auto. rewrite H1b. auto.
  - left. repeat split; auto. rewrite H1b. auto.
  - right. left. exists a2. exists t2. repeat split; auto. rewrite H1b. auto.
  - left. repeat split; auto. rewrite H1b. auto.
  - right. right. exists a3. exists t3. repeat split; auto. rewrite H1b. auto.
  - right. left. exists a1. exists t1. repeat split; auto.
    + rewrite H1b. auto.
    + rewrite <- H1c. rewrite H2a. rewrite H2c. auto.
  - right. right. exists a2. exists t2. repeat split; auto.
    + rewrite H1b. auto.
    + rewrite <- H1c. rewrite H2a. rewrite H2c. auto.
Qed.

Arguments vars_addr_join_assoc1 [J1 J2 J3 J12 J123].

Lemma vars_addr_join_assoc2: forall J1 J2 J3 J23 J123,
  vars_addr_join J2 J3 J23 ->
  vars_addr_join J1 J23 J123 ->
  exists J12,
  vars_addr_join J1 J2 J12 /\ vars_addr_join J12 J3 J123.
Proof.
  intros. apply vars_addr_join_comm in H, H0.
  pose proof (vars_addr_join_assoc1 H H0).
  destruct H1 as [J23' [H1 H2]].
  apply vars_addr_join_comm in H1, H2.
  exists J23'. auto.
Qed.

Definition prog_state_join (a b c : prog_state) : Prop :=
  vars_addr_join (vars_addr a) (vars_addr b) (vars_addr c) /\
  Mem.mem_join (mem a) (mem b) (mem c).

Lemma prog_state_join_comm : forall a b c,
  prog_state_join a b c ->
  prog_state_join b a c.
Proof.
  unfold prog_state_join. intros.
  destruct H. split.
  - apply vars_addr_join_comm. auto.
  - apply Mem.mem_join_comm. auto.
Qed.

Definition empty_prog_state : prog_state := mk_progstate empty_vars_addr Mem.empty_mem.

Definition prog_state_empty (a : prog_state) : Prop :=
  vars_addr_empty (vars_addr a) /\ Mem.mem_empty (mem a).

Lemma empty_prog_state_empty : prog_state_empty empty_prog_state.
Proof.
  unfold prog_state_empty, empty_prog_state. split.
  - apply empty_vars_addr_empty.
  - simpl. apply Mem.empty_mem_empty.
Qed.

Lemma prog_state_join_empty1 : forall a, prog_state_join empty_prog_state a a.
Proof.
  unfold prog_state_join, empty_prog_state. intros.
  split.
  - apply vars_addr_join_empty1.
  - apply Mem.mem_join_emp1.
Qed.

Lemma prog_state_join_empty2 : forall a, prog_state_join a empty_prog_state a.
Proof.
  unfold prog_state_join, empty_prog_state. intros.
  split.
  - apply vars_addr_join_empty2.
  - apply Mem.mem_join_emp2.
Qed.

Lemma prog_state_join_emp_l: forall a a1, prog_state_join empty_prog_state a a1 -> a1 = a.
Proof.
  unfold prog_state_join, empty_prog_state; intros.
  destruct a as [J m]; destruct a1 as [J1 m1]; simpl in *.
  destruct H as [H1 H2].
  f_equal.
  - apply vars_addr_join_emp_l; auto.
  - apply Mem.mem_join_emp_l; auto.
Qed.

Lemma prog_state_join_emp_r: forall a a1, prog_state_join a empty_prog_state a1 -> a1 = a.
Proof.
  intros. apply prog_state_join_comm in H.
  apply prog_state_join_emp_l in H. auto.
Qed.

Lemma prog_state_join_assoc2: forall a b c ab abc,
  prog_state_join a b ab ->
  prog_state_join ab c abc ->
  exists bc,
  prog_state_join b c bc /\ prog_state_join a bc abc.
Proof.
  unfold prog_state_join. intros.
  destruct H as [H1 H2]. destruct H0 as [H3 H4].
  pose proof (vars_addr_join_assoc1 H1 H3).
  pose proof (Mem.mem_join_assoc2 H2 H4).
  destruct H as [J23 [H5 H6]].
  destruct H0 as [m23 [H7 H8]].
  exists (mk_progstate J23 m23).
  repeat split; auto.
Qed.


Record FinDnt : Type := mk_Fin {
  NormalExit: prog_state -> prog_state -> Prop;
  BreakExit: prog_state -> prog_state -> Prop;
  ContExit: prog_state -> prog_state -> Prop;
  ReturnExit : prog_state -> prog_state -> Prop;
}.

Record prog_env : Type := {
  Structdef : list (ident * list (ident * SimpleCtype));
  Uniondef : list (ident * list (ident * SimpleCtype));
  struct_pos : int64 -> ident -> option int64;  (** calculate the position of field of struct *)
  union_pos : int64 -> ident -> option int64; (** calculate the position of field of union *)
  pred_size : ident -> Z;
}.

Definition state_eq (a b : prog_state) : Prop :=
  (forall i, option_eqb
    (fun a b : Mem.addr * SimpleCtype =>
         Mem.addr_eqb (fst a) (fst b) && SimpleCtype.eqb (snd a) (snd b))
    ((vars_addr a) i) ((vars_addr b) i) = true) /\
  (forall j, Mem.mem_var_eqb ((mem a) j) ((mem b) j) = true).

(* TODO: what does this function mean? Then, why is a struct size 0? *)
Fixpoint Ctype_size (x : SimpleCtype) : Z :=
  match x with
    | CT_basic (CT_void) => 1
    | CT_basic (CT_int _ I8) => 1
    | CT_basic (CT_int _ I16) => 2
    | CT_basic (CT_int _ I32) => 4
    | CT_basic (CT_int _ I64) => 8
    | CT_pointer _ => 8
    | CT_array t (Some len) => Ctype_size t * Z.max 0 len
    | CT_array t None => 0
    | CT_function _ _ => 1
    | CT_struct id _ => 0
    | CT_union id _ => 0
    | CT_enum id _ => 0
    | CT_alias s _ => 0
  end.

Definition Z_unop (op : CUop) (z : Z) : Z :=
  match op with
    | CO_NOTINT => Z.lnot z
    | CO_NOTBOOL => if (Z.eqb z 0) then 1%Z else 0%Z
    | CO_UMINUS => Z.opp z
    | CO_UPLUS => z
  end.

Definition Z_binop (op : CBinop) (z1 z2 : Z) : option Z :=
  match op with
    | CO_PLUS => Some (z1 + z2)
    | CO_MINUS => Some (z1 - z2)
    | CO_MUL => Some (z1 * z2)
    | CO_DIV => if (Z.eqb z2 0) then None else Some (z1 / z2)
    | CO_MOD => if (Z.eqb z2 0) then None else Some (Z.modulo z1 z2)
    | CO_AND => Some (Z.land z1 z2)
    | CO_OR => Some (Z.lor z1 z2)
    | CO_XOR => Some (Z.lxor z1 z2)
    | CO_SHL => Some (Z.shiftl z1 z2)
    | CO_SHR => Some (Z.shiftr z1 z2)
    | CO_EQ => Some (Z.b2z (Z.eqb z1 z2))
    | CO_NE => Some (Z.b2z (negb (Z.eqb z1 z2)))
    | CO_LT => Some (Z.b2z (Z.ltb z1 z2))
    | CO_GT => Some (Z.b2z (Z.gtb z1 z2))
    | CO_LE => Some (Z.b2z (Z.leb z1 z2))
    | CO_GE => Some (Z.b2z (Z.geb z1 z2))
    | CO_BAND => Some (Z.b2z (andb (negb (Z.eqb z1 0)) (negb (Z.eqb z2 0))))
    | CO_BOR => Some (Z.b2z (orb (negb (Z.eqb z1 0)) (negb (Z.eqb z2 0))))
  end.

Fixpoint expr_simple (x : Cexpr) : option Z :=
  match x with
    | C_const i t => Some i
    | C_unop op x' t => match expr_simple x' with
                          | Some i => Some (Z_unop op i)
                          | None => None
                        end
    | C_binop op x1 x2 t => match expr_simple x1 , expr_simple x2 with
                              | Some i1 , Some i2 => Z_binop op i1 i2
                              | _ , _ => None
                            end
    | C_sizeof x t => Some (Ctype_size x)
    | _ => None
  end.
