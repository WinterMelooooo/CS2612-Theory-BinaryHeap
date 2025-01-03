Require Import Classical_Prop.
Lemma imply_trans :forall p q : Prop, (p->q) <-> (~p\/q).
Proof.
    intros.
    split.
    -intros. pose proof classic p.
    destruct H0.
    --apply H in H0. right. apply H0.
    --left. apply H0.
    -intros. destruct H.
    --contradiction.
    --apply H.
Qed.

Lemma NN_Elim: forall p: Prop, ~~p<->p.
Proof.
    intros. tauto.
Qed.

Theorem cnf_trans_or: forall p1 p2 p3 : Prop, p3<->(p1\/p2) <-> (~p1\/p3) /\ (~p2 \/ p3) /\(p1\/p2\/~p3).
Proof.
    intros. split.
    -intros H. destruct H. tauto. 
    -intros H. destruct H as [H1 [H2 H3]]. tauto.
Qed.

Theorem cnf_trans_and: forall p1 p2 p3 : Prop, p3<->(p1/\p2) <-> (p1\/~p3) /\ (p2 \/ ~p3) /\(~p1\/~p2\/p3).
Proof.
    intros. split.
    -intros H. destruct H. tauto. 
    -intros H. destruct H as [H1 [H2 H3]]. tauto.
Qed.

Theorem cnf_trans_imply: forall p1 p2 p3 : Prop, p3<->(p1->p2) <-> (p1\/p3) /\ (~p2 \/ p3) /\(~p1\/p2\/~p3).
Proof.
    intros. split.
    -intros H. destruct H. tauto. 
    -intros H. destruct H as [H1 [H2 H3]]. tauto.
Qed.

Theorem cnf_trans_iff: forall p1 p2 p3 : Prop, p3<->(p1<->p2) <-> (p1\/p2\/p3) /\ (~p1\/~p2 \/ p3) /\(p1\/~p2\/~p3) /\ (~p1 \/p2\/~p3).
Proof.
    intros. split.
    -intros H. destruct H. tauto. 
    -intros H. destruct H as [H1 [H2 [H3 H4]]]. tauto.
Qed.

Theorem cnf_trans_not: forall p2 p3 : Prop, p3<->(~p2) <-> (p2\/p3) /\ (~p2 \/ ~p3) .
Proof.
    intros. split.
    -intros H. destruct H. tauto. 
    -intros H.  tauto.
Qed.

Theorem resol_1 : forall p q : Prop, (p\/q) -> (~p\/q) ->q .
Proof.
    intros. tauto.
Qed.

Require Import Coq.Setoids.Setoid.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope Z.

Theorem arith_mult1: forall x y : Z, x <= 0 -> y >= 0 -> x*y <= 0 .
Proof.
    intros. lia.
Qed.

Theorem arith_mult2: forall x y : Z, x <= 0 -> y <= 0 -> -x*y <= 0 .
Proof.
    intros. lia.
Qed.

Theorem arith_inequ_add: forall x y : Z, x <= 0 -> y <= 0 -> x+y <= 0 .
Proof.
    intros. lia.
Qed.

Theorem airth_fme : forall c d m n x y: Z, c>= 0 ->d <= 0 -> x + m <= 0 -> y + n <= 0 -> c*x - d*y + m*c - n*d <=0 .
Proof.
    intros. pose proof arith_mult1 (x+m) c  H1 H. pose proof arith_mult2 (y+n) d H2 H0.
    pose proof arith_inequ_add _ _ H3 H4. lia.
Qed.

Theorem uf_congurence : forall (A B:Type) (x y : A) (f: A->B), x = y -> f(x) = f(y) .
Proof.
    intros. rewrite H. reflexivity.
    
Qed.

Example smt_input: forall (x1 x2 x3 a1 a2 a3 : Z) (f:Z->Z) , ~(x2 >= x1 /\ x1 - x3 >= x2 /\ x3 >= 0 /\ a1 = a2 - a3 /\ a2 = f(x1) /\ a3 = f(x2) /\ ~(f(a1) = f(x3))).
Proof.
    intros. unfold not. intros. destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
    set (P := x1 = x2) .
    assert (P) as H8.
    { unfold P. lia. }
    unfold P in H8.
    assert (a2 = a3) as H9.
    { pose proof uf_congurence _ _ _ _ f H8. rewrite<-H5 in H. rewrite<-H6 in H. apply H. }
    assert (a1 = x3) as H10.
    { lia. }
    pose proof uf_congurence _ _ _ _ f H10. apply H7 in H. apply H.
Qed.


Theorem introduce_new_proposition :
  forall (p1 p2 : Prop), (p1 \/ p2) -> (p1 \/ p2).
Proof.
  intros p1 p2 H.
  remember (p1 -> p2) as p.
  (* Define the new proposition p as a logical expression *)
  (* Now, prove that p <-> (p1 \/ p2) *)
  assert (Hp: p <-> (p1 -> p2)).
  - subst p.  (* This step replaces p with (p1 \/ p2) in the proof context *)
    split.
    + intro H1. exact H1.
    + intro H2. exact H2.
- apply H.
Qed.

Theorem cnf_trans_and2: forall p1 p2 p3 : Prop, p3<->(p1/\p2) -> (p1\/~p3) /\ (p2 \/ ~p3) /\(~p1\/~p2\/p3).
Proof.
    intros. destruct H. tauto. 
Qed.

Theorem cnf_trans_not2: forall p2 p3 : Prop, p3<->(~p2) -> (p2\/p3) /\ (~p2 \/ ~p3) .
Proof.
    intros. destruct H. tauto. 
Qed.

Theorem resol_pos1: forall p1 p2 : Prop, p1->(~p1\/p2)->p2 .
Proof.
    intros. tauto.
Qed.

Theorem resol_pos2: forall p1 p2 : Prop, p1->(p2\/~p1)->p2 .
Proof.
    intros. tauto.
Qed. 

Theorem resol_neg1: forall p1 p2 : Prop, ~p1->(p1\/p2)->p2 .
Proof.
    intros. tauto.
Qed.

Theorem resol_neg2: forall p1 p2 : Prop, ~p1->(p2\/p1)->p2 .
Proof.
    intros. tauto.
Qed.

Theorem resol_false1: forall p1: Prop, p1->(~p1)->False .
Proof.
    intros. tauto.
Qed.

Theorem resol_false2: forall p1: Prop, ~p1->(p1)->False .
Proof.
    intros. tauto.
Qed.

Theorem demogan: forall p1 p2: Prop, (p1/\p2 ->False) <-> ((~p1) \/ (~p2)).
Proof.
    intros.
    split.
    -intros. tauto.
    -intros. tauto.
Qed.

Theorem uf_congurence2: forall (A B : Type) (x y : A) (f g : A->B), x = y -> f = g -> f x = g y .
Proof.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Theorem uf_test: forall (x1 x2 x3 y1 y2 y3 : Z)(f:Z->Z->Z->Z), x1 = y1 -> x2=y2 -> x3=y3 -> f x1 x2 x3 =f y1 y2 y3 .
Proof. 
    intros.
    assert(f = f) by reflexivity.
    pose proof uf_congurence2 _ _ _ _  f f H H2.
    pose proof uf_congurence2 _ _ _ _ _ _ H0 H3.
    pose proof uf_congurence2 _ _ _ _ _ _ H1 H4.
    exact H5.
    
Qed.

Theorem smt_proof : 
forall (x1: Z) (x2: Z) (x3: Z) (x4: Z) (x5: Z) (x6: Z) (f: Z->Z) (x9: Z) ,
(~(((((((((x1 >= x2) /\ ((x2 - x3) >= x1)) /\ (x3 >= 0)) /\ (x4 = (x5 - x6))) /\ (x5 = f(x2))) /\ (x6 = f(x1))) /\ (~((f(x4) = f(x3))))) /\ (2147483647 >= x9)))).
Proof.
intros. unfold not. intros. 
remember (x5 - x6) as x7 eqn: Purify_x7.
remember (x1 >= x2) as P1 eqn: HeqP1.
remember ((x2 - x3) >= x1) as P2 eqn: HeqP2.
remember (x3 >= 0) as P3 eqn: HeqP3.
remember (x4 = x7) as P4 eqn: HeqP4.
remember (x5 = f(x2)) as P5 eqn: HeqP5.
remember (x6 = f(x1)) as P6 eqn: HeqP6.
remember (f(x4) = f(x3)) as P7 eqn: HeqP7.
remember (2147483647 >= x9) as P8 eqn: HeqP8.
remember ((x5 - x6) = x7) as P9 eqn: HeqP9.
assert(H_purify9: P9).
{ subst P9. rewrite Purify_x7. reflexivity. }
remember (P1 /\ P2) as P10.
assert(HPP10: P10 <-> (P1 /\ P2)). {
subst P10.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP10 as HP10.
destruct HP10 as [HP101 [HP102 HP103]].
remember (P10 /\ P3) as P11.
assert(HPP11: P11 <-> (P10 /\ P3)). {
subst P11.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP11 as HP11.
destruct HP11 as [HP111 [HP112 HP113]].
remember (P11 /\ P4) as P12.
assert(HPP12: P12 <-> (P11 /\ P4)). {
subst P12.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP12 as HP12.
destruct HP12 as [HP121 [HP122 HP123]].
remember (P12 /\ P5) as P13.
assert(HPP13: P13 <-> (P12 /\ P5)). {
subst P13.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP13 as HP13.
destruct HP13 as [HP131 [HP132 HP133]].
remember (P13 /\ P6) as P14.
assert(HPP14: P14 <-> (P13 /\ P6)). {
subst P14.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP14 as HP14.
destruct HP14 as [HP141 [HP142 HP143]].
fold (~P7) in H.
remember (~(P7)) as P15.
assert(HPP15: P15 <-> (~(P7))). {
subst P15.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_not2 _ _  HPP15 as HP15.
destruct HP15 as [HP151 HP152].
remember (P14 /\ P15) as P16.
assert(HPP16: P16 <-> (P14 /\ P15)). {
subst P16.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP16 as HP16.
destruct HP16 as [HP161 [HP162 HP163]].
remember (P16 /\ P8) as P17.
assert(HPP17: P17 <-> (P16 /\ P8)). {
subst P17.
split.
+ intro H1. exact H1.
+ intro H2. exact H2.
}
pose proof cnf_trans_and2 _ _ _ HPP17 as HP17.
destruct HP17 as [HP171 [HP172 HP173]].
assert(TP1: (P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ ~P7 /\ P8 /\ P9)->False). {
intros H1.
destruct H1 as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
rewrite HeqP1 in H1.
rewrite HeqP2 in H2.
rewrite HeqP3 in H3.
rewrite HeqP4 in H4.
rewrite HeqP5 in H5.
rewrite HeqP6 in H6.
rewrite HeqP7 in H7.
rewrite HeqP8 in H8.
rewrite HeqP9 in H9.
assert(LP1: (x1 = x2)) by lia. 
assert(LP2: (x2 = x1)) by lia. 
assert(LP3: (f(x2) = f(x1))). {
assert (H_UF0: f = f) by reflexivity.
assert(H_P0: (x2 = x1)) by lia.
pose proof uf_congurence2 _ _ _ _ _ _ H_P0 H_UF0 as H_UF1.
exact H_UF1.
}
assert(LP4: (x5 = f(x1))) by lia. 
assert(LP5: (f(x1) = x6)) by lia. 
assert(LP6: (x5 = x6)) by lia. 
assert(LP7: (x3 = x4)) by lia. 
assert(LP8: (f(x3) = f(x4))). {
assert (H_UF0: f = f) by reflexivity.
assert(H_P0: (x3 = x4)) by lia.
pose proof uf_congurence2 _ _ _ _ _ _ H_P0 H_UF0 as H_UF1.
exact H_UF1.
}
assert(LP9: (f(x4) = f(x3))) by lia. 
contradiction.
}
assert(RTP1: ((~(P1)) \/ (~(P2)) \/ (~(P3)) \/ (~(P4)) \/ (~(P5)) \/ (~(P6)) \/ P7 \/ (~(P8)) \/ (~(P9))) ). {
pose proof demogan (P1) (P2 /\P3 /\P4 /\P5 /\P6 /\~P7 /\P8 /\P9) as DP1. rewrite DP1 in TP1.
pose proof demogan (P2) (P3 /\P4 /\P5 /\P6 /\~P7 /\P8 /\P9) as DP2. rewrite DP2 in TP1.
pose proof demogan (P3) (P4 /\P5 /\P6 /\~P7 /\P8 /\P9) as DP3. rewrite DP3 in TP1.
pose proof demogan (P4) (P5 /\P6 /\~P7 /\P8 /\P9) as DP4. rewrite DP4 in TP1.
pose proof demogan (P5) (P6 /\~P7 /\P8 /\P9) as DP5. rewrite DP5 in TP1.
pose proof demogan (P6) (~P7 /\P8 /\P9) as DP6. rewrite DP6 in TP1.
pose proof demogan (~P7) (P8 /\P9) as DP7. rewrite DP7 in TP1.
pose proof NN_Elim P7 as NDP7. rewrite NDP7 in TP1.
pose proof demogan (P8) (P9) as DP8. rewrite DP8 in TP1.
exact TP1.
}
pose proof resol_pos2 _ _ H HP171 as H_resol2.
pose proof resol_pos2 _ _ H HP172 as H_resol3.
pose proof resol_pos2 _ _ H_resol2 HP161 as H_resol4.
pose proof resol_pos2 _ _ H_resol2 HP162 as H_resol5.
pose proof resol_pos2 _ _ H_resol5 HP152 as H_resol6.
pose proof resol_pos2 _ _ H_resol4 HP141 as H_resol7.
pose proof resol_pos2 _ _ H_resol4 HP142 as H_resol8.
pose proof resol_pos2 _ _ H_resol7 HP131 as H_resol9.
pose proof resol_pos2 _ _ H_resol7 HP132 as H_resol10.
pose proof resol_pos2 _ _ H_resol9 HP121 as H_resol11.
pose proof resol_pos2 _ _ H_resol9 HP122 as H_resol12.
pose proof resol_pos2 _ _ H_resol11 HP111 as H_resol13.
pose proof resol_pos2 _ _ H_resol11 HP112 as H_resol14.
pose proof resol_pos2 _ _ H_resol13 HP101 as H_resol15.
pose proof resol_pos2 _ _ H_resol13 HP102 as H_resol16.
pose proof resol_pos1 _ _ H_resol15 RTP1 as H_resol17.
pose proof resol_pos1 _ _ H_resol16 H_resol17 as H_resol18.
pose proof resol_pos1 _ _ H_resol14 H_resol18 as H_resol19.
pose proof resol_pos1 _ _ H_resol12 H_resol19 as H_resol20.
pose proof resol_pos1 _ _ H_resol10 H_resol20 as H_resol21.
pose proof resol_pos1 _ _ H_resol8 H_resol21 as H_resol22.
pose proof resol_neg1 _ _ H_resol6 H_resol22 as H_resol23.
pose proof resol_pos1 _ _ H_resol3 H_resol23 as H_resol24.
pose proof resol_false1 _ H_purify9 H_resol24 as Hend.
apply Hend.
Qed.

Theorem smt_proof : 
forall (x1: Z) (x2: Z) (x3: Z) (x4: Z) (x5: Z) (x6: Z) (f: Z->Z) (x9: Z) ,
~(((((((((x1 >= x2) /\ ((x2 - x3) >= x1)) /\ (x3 >= 0)) /\ (x4 = (x5 - x6))) /\ (x5 = f(x2))) /\ (x6 = f(x1))) /\ ~((f(x4) = f(x3)))) /\ (2147483647 >= x9))).
Proof.
intros. unfold not. intros. 
remember(x5 - x6) as x7 eqn: Purify_x7.
remember(x1 >= x2) as P1 .
remember((x2 - x3) >= x1) as P2 .
remember(x3 >= 0) as P3 .
remember(x4 = x7) as P4 .
remember(x5 = f(x2)) as P5 .
remember(x6 = f(x1)) as P6 .
remember(f(x4) = f(x3)) as P7 eqn: HeqP7.
remember(2147483647 >= x9) as P8 .
remember((x5 - x6) = x7) as P9 .
assert(P9).
{ subst P9. rewrite Purify_x7. reflexivity. }
(* fold (~P7) in H. *)
remember (P1 /\ P2) as P10.
assert(HPP10: P10 <-> (P1 /\ P2)). {
    subst P10.
    split.
    + intro H1. exact H1.
    + intro H2. exact H2.
}
pose proof cnf_trans_and2 P1 P2 P10 HPP10 as HP10.
destruct HP10 as [HP101 [HP102 HP103]].
remember (P10 /\ P3) as P11.
assert(HPP11: P11 <-> P10 /\ P3). {
    subst P11.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP11 as HP11.
destruct HP11 as [HP111 [HP112 HP113]].
remember (P11 /\ P4) as P12.
assert(HPP12: P12 <-> P11 /\ P4). {
    subst P12.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP12 as HP12.
destruct HP12 as [HP121 [HP122 HP123]].
remember (P12 /\ P5) as P13.
assert(HPP13: P13 <-> P12 /\ P5). {
    subst P13.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP13 as HP13.
destruct HP13 as [HP131 [HP132 HP133]].
remember (P13 /\ P6) as P14.
assert(HPP14: P14 <-> P13 /\ P6). {
    subst P14.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP14 as HP14.
destruct HP14 as [HP141 [HP142 HP143]].
fold (~P7) in H.
remember (~P7) as P15.
assert(HPP15: P15<-> ~P7). {
    subst P15.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_not2 _ _ HPP15 as HP15.
destruct HP15 as [HP151 HP152].
remember (P14 /\ P15) as P16.
assert(HPP16: P16 <-> P14 /\ P15). {
    subst P16.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP16 as HP16.
destruct HP16 as [HP161 [HP162 HP163]].
remember (P16 /\ P8) as P17.
assert(HPP17: P17 <-> P16 /\ P8). {
    subst P17.
    split.
    + intro H2. exact H2.
    + intro H1. exact H1.
}
pose proof cnf_trans_and2 _ _ _ HPP17 as HP17.
destruct HP17 as [HP171 [HP172 HP173]].
assert(P18: (P1 /\ P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ ~P7 /\ P8 /\ P9)->False). {
    intros.
    destruct H1 as[H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
    rewrite HeqP1 in H1.
    rewrite HeqP2 in H2.
    rewrite HeqP3 in H3.
    rewrite HeqP4 in H4.
    rewrite HeqP5 in H5.
    rewrite HeqP6 in H6.
    rewrite HeqP7 in H7.
    rewrite HeqP8 in H8.
    rewrite HeqP9 in H9.
    
    assert(1*x5 - 1*x6 - 1*x7 = 0) by lia.
    assert(x9 - 2147483647 <= 0) by lia.
    assert(1*x4 - 1*x7 = 0) by lia.
    assert(-1*x3 <= 0) by lia.
    assert(1*x1 - 1*x2 + 1*x3 <= 0) by lia.
    assert(-1*x1 + 1*x2 <= 0) by lia.
    assert(-1*x4 + 1*x7 = 0) by lia.
    assert(1*x1 -1*x2 <= 0) by lia.
    assert(-1*x1+1*x2 <= 0) by lia.
    assert(x1 = x2) by lia.
    assert(x2 = x1) by lia.
    assert(LP10 : f(x2) = f(x1)). {
        pose proof uf_congurence _ _ _ _ f H20 as H21.
        apply H21.
    }
    assert( x5 = x6) by lia.
    assert(x3 = x4) by lia.
    assert(f(x3) = f(x4)). {
        pose proof uf_congurence _ _ _ _ f H22.
        apply H23.
    }
    assert(f(x4) = f(x3)) by lia.
    contradiction.
}
assert(~P1 \/ ~P2 \/ ~P3 \/ ~P4 \/ ~P5\/ ~P6 \/ P7 \/ ~P8 \/ ~P9). {   
       pose proof demogan P1 (P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ ~ P7 /\ P8 /\ P9). rewrite H1 in P18.
       pose proof demogan P2 (P3 /\ P4 /\ P5 /\ P6 /\ ~ P7 /\ P8 /\ P9). rewrite H2 in P18.
       pose proof demogan P3 (P4 /\ P5 /\ P6 /\ ~ P7 /\ P8 /\ P9). rewrite H3 in P18.
       pose proof demogan P4 (P5 /\ P6 /\ ~ P7 /\ P8 /\ P9). rewrite H4 in P18.
       pose proof demogan P5 (P6 /\ ~ P7 /\ P8 /\ P9). rewrite H5 in P18.
       pose proof demogan P6 ( ~ P7 /\ P8 /\ P9). rewrite H6 in P18.
       pose proof demogan (~P7) (P8 /\ P9). rewrite H7 in P18.
       pose proof NN_Elim P7 as H77.
       rewrite H77 in P18.
       pose proof demogan P8 (P9). rewrite H8 in P18.
       exact P18. 
}
pose proof resol_pos2 _ _ H HP171.
pose proof resol_pos2 _ _ H HP172.
pose proof resol_pos2 _ _ H2 HP161.
pose proof resol_pos2 _ _ H2 HP162.
pose proof resol_pos2 _ _ H5 HP152.
pose proof resol_pos2 _ _ H4 HP141.
pose proof resol_pos2 _ _ H4 HP142.
pose proof resol_pos2 _ _ H7 HP131.
pose proof resol_pos2 _ _ H7 HP132.
pose proof resol_pos2 _ _ H9 HP121.
pose proof resol_pos2 _ _ H9 HP122.
pose proof resol_pos2 _ _ H11 HP111.
pose proof resol_pos2 _ _ H11 HP112.
pose proof resol_pos2 _ _ H13 HP101.
pose proof resol_pos2 _ _ H13 HP102.
pose proof resol_pos1 _ _ H15 H1.
pose proof resol_pos1 _ _ H16 H17.
pose proof resol_pos1 _ _ H14 H18.
pose proof resol_pos1 _ _ H12 H19.
pose proof resol_pos1 _ _ H10 H20.
pose proof resol_pos1 _ _ H8 H21.
pose proof resol_neg1 _ _ H6 H22.
pose proof resol_pos1 _ _ H3 H23.
pose proof resol_false1 _  H0 H24.
apply H25.
unfold not in H24.
apply H24.
apply H0.
Qed.