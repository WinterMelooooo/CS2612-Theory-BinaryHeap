From SimpleC.ASRT Require Import DefFiles.
From SimpleC.CSE Require Import Cexpr_def.

Section Eval_proof_version.

Variable C : Ctype.
Variable class_E : Class_E C.
Variable SepT : Separation_def C class_E.
Variable Split_f : assertion -> expr_val -> option (Assertion).

Record call_wit : Type := mk_wit {
  pre_call : assertion;
  f_call : expr_val;
  arg_call : list expr_val;
  posts_call : option (list (expr_val * assertion)); (** Use Something to represent No return *)
}.

Definition Call_use_wit (wit : list call_wit) (pre : assertion) (f : expr_val) (arg :list expr_val) : option (list (expr_val * assertion)) * list call_wit :=
  match wit with
    | nil => (None , nil)
    | h :: l' => if (Assertion_eqb pre (pre_call h) && eqb_val f (f_call h) && eqb_val_orderedlist arg (arg_call h)) then 
                                            (posts_call h , l')
                                          else (None , l')
  end.

Fixpoint list_apply_f {A B C D:Type} (f : A -> B -> C -> D * A) (l : list C)(a : A) (b : B) : list D * A :=
  match l with
    | nil => (nil , a) 
    | c :: l' => let (nd , na) := f a b c in 
                 let (ld , la) := list_apply_f f l' na b in 
                  (nd :: ld , la)
  end.  

Fixpoint eval_Cexprval (x : Cexpr) (call_oracle_wit : list call_wit) (Asrt : assertion) : option (list (expr_val * assertion)) * list call_wit :=
  match x with
  | C_const i t => (Some ((EConstZ i , Asrt) :: nil) , call_oracle_wit)
  | C_deref x' t =>
    match (eval_Cexprval x' call_oracle_wit  Asrt) with
      | (None,wit) => (None,wit)
      | (Some l,wit) => (Some_concat (map (fun a =>  match Split_f (snd a) (fst a) with
                                                 | None => None 
                                                 | Some l' => let val_ret := map (fun b => eval_val (Sep_list (Split_assert b)) (fst a)) l' in
                                                               if (Find_None val_ret) then None else Some (combine (Clear_option val_ret) l')
                                                end) l),wit)  
    end 
  | C_addrof x' t => eval_Cexprval_l x' call_oracle_wit Asrt 
  | C_unop op x' t => 
      match (eval_Cexprval x' call_oracle_wit Asrt) with
        | (None , wit) => (None , wit) 
        | (Some l, wit) => (Some (map (fun a => (match op with
                                          | O_NOTINT => Vuop Oneg (fst a)
                                          | O_NOTBOOL => Vuop Onot (fst a)
                                          | O_UMINUS => Vuop Oneg (fst a)
                                          | O_UPLUS => (fst a)
                                        end , snd a)) l),wit) 
      end
  | C_binop op x1 x2 t =>
      match (eval_Cexprval x1 call_oracle_wit Asrt) with
      | (None , wit) => (None , wit)
      | (Some l1 , wit) => let (ans , final_wit) := (fix f_list (l : Assertion) (w : list call_wit) :=
                                                                    match l with 
                                                                      | nil => (nil , w)
                                                                      | c :: l' => let (nd , nw) := eval_Cexprval x2 w c in 
                                                                                   let (ld , lw) := f_list l' nw in
                                                                                   (nd :: ld , lw)   
                                                                    end) (map (fun a => snd a) l1) wit in 
                            match Some_concat (map (fun a => 
                              match snd a with
                                | None => None  
                                | Some l2 => Some ((map (fun b => match op with
                                                          | O_PLUS => Some ((Vbop Oadd (fst a) (fst b) , snd b) :: nil)
                                                          | O_MINUS => Some ((Vbop Osub (fst a) (fst b) , snd b) :: nil)
                                                          | O_MUL => Some ((Vbop Omul (fst a) (fst b) , snd b) :: nil) 
                                                          | O_DIV => Some ((Vbop Odiv (fst a) (fst b) , snd b) :: nil) 
                                                          | O_MOD => Some ((Vbop Omod (fst a) (fst b) , snd b) :: nil) 
                                                          | O_AND => Some ((Vbop Oand (fst a) (fst b) , snd b) :: nil)  
                                                          | O_OR => Some ((Vbop Oor (fst a) (fst b) , snd b) :: nil)
                                                          | O_XOR => Some ((Vbop Oxor (fst a) (fst b) , snd b) :: nil)   
                                                          | O_SHL => Some ((Vbop Oshl (fst a) (fst b) , snd b) :: nil)
                                                          | O_SHR => Some ((Vbop Oshr (fst a) (fst b) , snd b) :: nil) 

                                                          | O_EQ => Some ((Vtrue , Prop_add (Be Pvequal (fst a) (fst b)) (snd b)) :: (Vfalse , Prop_add (Up Pnot (Be Pvequal (fst a) (fst b))) (snd b) ) :: nil)
                                                          | O_NE => Some ((Vtrue , Prop_add (Up Pnot (Be Pvequal (fst a) (fst b))) (snd b)) :: (Vfalse , Prop_add (Be Pvequal (fst a) (fst b)) (snd b)) :: nil)
                                                          | O_LT => Some ((Vtrue, Prop_add (Be Pvlt (fst a) (fst b)) (snd b)) :: (Vfalse, Prop_add (Be Pvge (fst a) (fst b)) (snd b)) :: nil)
                                                          | O_GT => Some ((Vtrue, Prop_add (Be Pvgt (fst a) (fst b)) (snd b)) :: (Vfalse, Prop_add (Be Pvle (fst a) (fst b)) (snd b)) :: nil)       
                                                          | O_LE => Some ((Vtrue, Prop_add (Be Pvle (fst a) (fst b)) (snd b)) :: (Vfalse, Prop_add (Be Pvgt (fst a) (fst b)) (snd b)) :: nil)   
                                                          | O_GE => Some ((Vtrue, Prop_add (Be Pvge (fst a) (fst b)) (snd b)) :: (Vfalse, Prop_add (Be Pvlt (fst a) (fst b)) (snd b)) :: nil)

                                                          | O_BAND => None 
                                                          | O_BOR => None
                                                         end
                                              ) l2))
                            end) (combine (map (fun a => fst a) l1) ans)) with
                              | None => (None , final_wit)
                              | Some ans_l => (Some_concat ans_l , final_wit)
                            end
    end
  | C_cast x t => eval_Cexprval x call_oracle_wit  Asrt
  | C_structfield x' id t =>
      match (eval_Cexprval_l x' call_oracle_wit Asrt) with
      | (None , wit) => (None, wit)
      | (Some l , wit) => (Some_concat (map (fun a =>  match Split_f (snd a) (EField (fst a) id) with
                                                | None => None 
                                                | Some l' => let val_ret := map (fun b => eval_val (Sep_list (Split_assert b)) (EField (fst a) id)) l' in 
                                                  if (Find_None val_ret) then None else Some (combine (Clear_option val_ret) l')   
                                    end) l), wit) 
      end
  | C_unionfield x' id t =>
      match (eval_Cexprval_l x' call_oracle_wit Asrt) with
      | (None , wit) => (None, wit)
      | (Some l , wit) => (Some_concat (map (fun a =>  match Split_f (snd a) (Vunion_address (fst a) (Some id)) with
                                                | None => None 
                                                | Some l' => let val_ret := map (fun b => eval_val (Sep_list (Split_assert b)) (Vunion_address (fst a) (Some id))) l' in 
                                                  if (Find_None val_ret) then None else Some (combine (Clear_option val_ret) l')   
                                    end) l) , wit)
      end 
  | C_sizeof t1 t => (Some (((EConstZ (Ctype_size t1)) , Asrt) :: nil) , call_oracle_wit ) 
  | C_call f arg t => 
     match (eval_Cexprval_list arg call_oracle_wit Asrt) with
       | (None, wit) => (None , wit) 
       | (Some l1, wit) => let (f_cal_list , after_f_cal_wit) := (fix f_list (l : Assertion) (w : list call_wit) :=
                                                                    match l with 
                                                                      | nil => (nil , w)
                                                                      | c :: l' => let (nd , nw) := eval_Cexprval f w c in 
                                                                                   let (ld , lw) := f_list l' nw in
                                                                                   (nd :: ld , lw)   
                                                                    end) (map (fun a => snd a) l1) wit in 
                           let (return_posts , return_wits ) := list_apply_f  (fun wit' _ f_msg => match snd f_msg with 
                                                                 | None => (None , wit')
                                                                 | Some args_l => let (one_posts , one_wits) := list_apply_f (fun wits f_args f_val_and_asrt => Call_use_wit wits (snd f_val_and_asrt) (fst f_val_and_asrt) f_args) args_l wit' (fst f_msg) in 
                                                                  (Some_concat one_posts , one_wits) 
                                                                end ) (combine (map (fun a => fst a) l1) f_cal_list) after_f_cal_wit tt in 
                             ( Some_concat return_posts, return_wits)
     end
  | C_index arr id t => match (eval_Cexprval_l arr call_oracle_wit Asrt) with 
                         | (None , wit) => (None , wit) 
                         | (Some l , wit) => match Some_concat (map (fun a => match Split_f (snd a) (fst a) with
                                                                          | None => None 
                                                                          | Some l' => let val_ret := map (fun b => eval_val (Sep_list (Split_assert b)) (fst a)) l' in 
                                                                                       if (Find_None val_ret) then None else Some (combine (Clear_option val_ret) l')   
                                                                        end) l) with 
                                               | None => (None , wit)
                                               | Some newl => let (ans , final_wit) := (fix f_list (l1 : Assertion) (w : list call_wit) :=
                                                                                            match l1 with 
                                                                                              | nil => (nil , w)
                                                                                              | c :: l' => let (nd , nw) := eval_Cexprval id w c in 
                                                                                                           let (ld , lw) := f_list l' nw in
                                                                                                              (nd :: ld , lw)   
                                                                                            end) (map (fun a => snd a) newl) wit in 
                                                              (Some_concat (map (fun a => match snd a with 
                                                                                            | None => None 
                                                                                            | Some ans' => Some (map (fun b => (Vlop Vnth (fst b) (fst a) , snd b)) ans') 
                                                                                          end ) (combine (map (fun a => fst a) newl) ans)) , final_wit)
                                             end 
                        end
  | _ => (None , call_oracle_wit)
  end
  
with eval_Cexprval_l (x : Cexpr) (call_oracle_wit : list call_wit) (Asrt : assertion) : option (list (expr_val * assertion)) * list call_wit :=
  match x with
  | C_var id t => (eval_Ctmpval Asrt id , call_oracle_wit)
  | C_deref x' t => eval_Cexprval x' call_oracle_wit Asrt
  | C_structfield x' id t =>
      match eval_Cexprval_l x' call_oracle_wit Asrt with
      | (None , wit) => (None , wit)
      | (Some l , wit) => (Some (map (fun a => ((EField (fst a) id) , snd a)) l) , wit) 
      end
  | C_unionfield x' id t =>
      match (eval_Cexprval_l x' call_oracle_wit  Asrt) with
      | (None , wit) => (None , wit)
      | (Some l , wit) => (Some (map (fun a => ((Vunion_address (fst a) (Some id)) , snd a)) l) , wit)
      end 
  | C_index arr id t => match (eval_Cexprval_l arr call_oracle_wit Asrt) with 
                         | (None , wit) => (None , wit) 
                         | (Some l , wit) => let (ans , final_wit) := (fix f_list (l1 : Assertion) (w : list call_wit) :=
                                                                          match l1 with 
                                                                            | nil => (nil , w)
                                                                            | c :: l' => let (nd , nw) := eval_Cexprval id w c in 
                                                                                         let (ld , lw) := f_list l' nw in
                                                                                        (nd :: ld , lw)   
                                                                          end) (map (fun a => snd a) l) wit in 
                                              (Some_concat (map (fun a => match snd a with 
                                                                            | None => None 
                                                                            | Some ans' => Some (map (fun b => (Vlop Vnth (fst b) (fst a) , snd b)) ans') 
                                                                          end ) (combine (map (fun a => fst a) l) ans)) , final_wit)
                        end
  | _ => (None , call_oracle_wit) 
  end

with eval_Cexprval_list (x : Cexpr_list) (call_oracle_wit : list call_wit) (Asrt : assertion) : option (list (list expr_val * assertion)) * list call_wit :=
  match x with
    | CL_nil => (Some ((nil , Asrt) :: nil) , call_oracle_wit)
    | CL_cons x' l' => match eval_Cexprval x' call_oracle_wit Asrt with
                         | (None , wit) => (None , wit) 
                         | (Some l1 , wit) => let (return_l , return_wit) := (fix f_list (l0 : list (expr_val * assertion)) (w : list call_wit) : list (option (list (list expr_val * assertion))) * list call_wit :=
                                                                                    match l0 with
                                                                                      | nil => (nil , w) 
                                                                                      | c :: l0' => let (nd , nw) := eval_Cexprval_list l' w (snd c) in 
                                                                                                    let (ld , lw) := f_list l0' nw in 
                                                                                                    match nd with 
                                                                                                      | None => (nd :: ld , lw)
                                                                                                      | Some expr_l => (Some (map (fun b => ((fst c) :: (fst b) , (snd b))) expr_l) :: ld , lw)
                                                                                                    end  
                                                                                    end) l1 wit in 
                                               (Some_concat return_l , return_wit)
                       end
  end.
  
End Eval_proof_version. 