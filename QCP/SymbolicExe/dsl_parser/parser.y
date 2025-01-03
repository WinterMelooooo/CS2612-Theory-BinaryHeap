%locations
%define parse.error verbose

%{
  #include <stdio.h>
  #include <stdlib.h>
  #include <string.h>
  #include "lang.h"
  #include "lexer.h"
  #include "../compiler/utils.h"
  void llerror(char*);
  int lllex(void);
  struct lang_rule_file *root;
  int flag_exist =0;
  int flag_atom = 0;
  int isAssigned;
  struct var_list{
    char *var;
    struct var_list *tail;
  };
  int isExistVar(struct var_list **vars,char *name);
  void addVar(struct var_list **vars,char *name);
  void clearVarList(struct var_list **vars);
  struct var_list *evars = NULL;
  struct var_list *svars = NULL;
%}

%define api.prefix{ll}

%union {
  unsigned long long nat;
  char *s;
  char *p;
  struct lang_expr *lang_expr;
  struct lang_expr_list *lang_expr_list;
  struct lang_cmd *lang_cmd;
  struct lang_pattern *lang_pattern;
  struct lang_pattern_list *lang_pattern_list;
  struct lang_priority *lang_priority;
  struct lang_priority_list *lang_priority_list;
  struct lang_action *lang_action;
  struct lang_action_list *lang_action_list;
  struct lang_rule_list *lang_rule_list;
  struct PatternPolyType *PatternPolyType;
  struct PatternPolyTypeList *PatternPolyTypeList;
  struct PatternCType *PatternCType;
  struct StringList *stringList;
  struct lang_rule_file *rule_file;
}

//terminals

%token <nat> NAT
%token <s> IDENT
%token <p> PATH

%token <none> ID
%token <none> PRIO
%token <none> LEFT
%token <none> RIGHT
%token <none> ACTION
%token <none> CHECK


%token <none> UPPER_NULL
%token <none> LOWER_NULL
%token <none> I8
%token <none> I16 
%token <none> I32
%token <none> U8
%token <none> U16
%token <none> U32
%token <none> I64
%token <none> U64
%token <none> PTR 

%token <none> HASH
%token <none> LPAREN
%token <none> RPAREN
%token <none> LBRACKET
%token <none> RBRACKET
%token <none> LBRACES
%token <none> RBRACES
%token <none> SEMI
%token <none> COLON
%token <none> COMMA
%token <none> DQUATATION
%token <none> DOT

%token <none> QUEST
%token <none> PLUS
%token <none> MINUS
%token <none> MULT
%token <none> DIV

%token <none> MINUSGREATER
%token <none> EQ
%token <none> NEQ
%token <none> LT
%token <none> GT
%token <none> LE
%token <none> GE
%token <none> AT
%token <none> OR

%token <none> EXISTS
%token <none> ATOM
%token <none> SIZEOF
%token <none> INCLUDE
%token <none> DATA_AT
%token <none> UNDEF_DATA_AT
%token <none> FIELDADDR

%token <none> PT_VOID
%token <none> PT_CHAR
%token <none> PT_INT
%token <none> PT_LONG
%token <none> PT_UNSIGNED
%token <none> PT_STRUCT
%token <none> PT_UNION
%token <none> PT_ENUM

//nonterminals
%type <rule_file> WHOLE
%type <stringList> INCLUDE_PATHS
%type <p> INCLUDE_PATH
%type <lang_rule_list> RULES
%type <lang_cmd> CMD
%type <nat> CMD_ID
%type <lang_priority_list> CMD_PRIO
%type <lang_priority> PRIOS
%type <lang_priority_list> CMD_PRIOS
%type <lang_pattern_list> CMD_PATTERNS
%type <lang_pattern_list> CMD_PATTERN
%type <lang_pattern_list> PATTERNS
%type <lang_pattern> PATTERN
%type <lang_action_list> CMD_CHECK
%type <lang_action_list> CMD_ACTION
%type <lang_action> ACT
%type <lang_action_list> ACTS
%type <s> NAME_S
%type <lang_expr> NAME
%type <lang_expr> EXPR
%type <lang_expr> EXPR0
%type <lang_expr> EXPR1
%type <lang_expr> EXPR_TOP
%type <lang_expr> EXPR_PREDS
%type <lang_expr> EXPR_BOOLEAM
%type <lang_expr> EXPR_ARITH
%type <lang_expr> EXPR_MultDiv
%type <lang_expr> EXPR_Uop
%type <lang_expr> EXPR_BASE
%type <lang_expr> EXPR_FUNC
%type <lang_expr> EXPR_SEP
%type <lang_expr> EXPR_EXIST
%type <lang_expr> EXPR_ATOM
%type <lang_expr_list> EXPRS
%type <PatternCType> CType_IDENT
%type <PatternCType> CType
%type <PatternCType> Basic_Ctype
%type <PatternPolyType> POLYTYPE
%type <PatternPolyType> POLYTYPE_BASE
%type <PatternPolyTypeList> POLYTYPES

%%

WHOLE:
    INCLUDE_PATHS RULES
    {
        $$ = lang_RF($1,$2);
        root = $$;
    }
  | RULES
    {
        $$ = lang_RF(StringListNil(),$1);
        root = $$;
    }

INCLUDE_PATHS:
    INCLUDE_PATH
    { $$ = StringListCons(strdup($1),StringListNil());}
  | INCLUDE_PATH INCLUDE_PATHS
    { $$ = StringListCons(strdup($1),$2);}

INCLUDE_PATH:
    HASH INCLUDE LT PATH GT
    { $$ = $4; }
  | HASH INCLUDE DQUATATION PATH DQUATATION
    { $$ = $4; }

RULES:
    CMD
    { $$ = lang_RLCons($1,lang_RLNil()); }
  | CMD RULES
    { $$ = lang_RLCons($1,$2); }

CMD:
    CMD_ID CMD_PRIO CMD_PATTERNS CMD_CHECK CMD_ACTION
    { $$ = lang_cmd($1, $2, $3, $5, $4);}
  | CMD_ID CMD_PRIO CMD_PATTERNS CMD_ACTION
    { $$ = lang_cmd($1, $2, $3, $4, NULL);}

CMD_ID:
    ID COLON NAT
    { $$ = $3; }

CMD_PRIO:
    PRIO COLON CMD_PRIOS
    { $$ = $3; }

PRIOS:
   IDENT LPAREN NAT RPAREN
   { $$ = lang_PR($1, $3);}

CMD_PRIOS :
    PRIOS
    {$$ = lang_PRCons($1, lang_PRNil());}
  | PRIOS COMMA CMD_PRIOS
    {$$ = lang_PRCons($1, $3);}

CMD_PATTERNS:
    CMD_PATTERN
    { $$ = $1; }
  | CMD_PATTERN CMD_PATTERNS
    { $$ = lang_TPatternListApp($1, $2);}

CMD_PATTERN:
    LEFT COLON PATTERNS 
    { $$ = lang_TPatternList($3, lang_T_LEFT); } 
  | RIGHT COLON PATTERNS
    { $$ = lang_TPatternList($3, lang_T_RIGHT); }

PATTERNS:
    PATTERN
    { $$ = lang_PTLCons($1, lang_PTLNil()); }
  | PATTERN PATTERNS 
    { $$ = lang_PTLCons($1, $2);}

PATTERN:
    EXPR AT NAT
    { $$ = lang_TPattern($1, $3);}

CMD_CHECK:
    CHECK COLON ACTS
    { $$ = $3; }

CMD_ACTION:
    ACTION COLON ACTS
    { $$ = $3; }

ACT:
    IDENT LPAREN EXPR_TOP RPAREN SEMI
    { $$ = lang_TAction($1,$3);}

ACTS:
    ACT
    { $$ = lang_ALCons($1,lang_ALNil()); }
  | ACT ACTS
    { $$ = lang_ALCons($1,$2); }

EXPRS:
    EXPR_ARITH 
    { $$ = lang_PLCons($1,lang_PLNil()); }
  | EXPR_ARITH COMMA EXPRS
    { $$ = lang_PLCons($1,$3); }

EXPR_EXIST:
    EXISTS IDENT COMMA
    {
      flag_exist = flag_exist+1;
      addVar(&evars,$2);
    }

EXPR_ATOM:
    ATOM IDENT COMMA
    {
      flag_atom = flag_atom+1;
      addVar(&svars,$2);
    }

EXPR:
    EXPR_EXIST EXPR
    {
      $$ = $2;
      flag_exist = flag_exist-1;
      if(flag_exist == 0){
          clearVarList(&evars);
      }
  }
  | EXPR_ATOM EXPR
    {
      $$ = $2;
      flag_atom = flag_atom -1;
      if(flag_atom ==0){
        clearVarList(&svars);
      }
    }
  | EXPR_TOP 
    { $$ = $1; }

EXPR0:
    NAT
    { $$ = lang_TConst($1); }
  | IDENT
    { 
      isAssigned = 0;
      if(flag_exist !=0){
        if(isExistVar(&evars,$1)==1){
          $$ = lang_TVar($1,NULL,EXISTS_VAR);
          isAssigned = 1;
        }
      }
      if(flag_atom != 0 ){
        if(isExistVar(&svars,$1)==1){
          $$ = lang_TVar($1,NULL,ATOM_VAR);
          isAssigned = 1;
        }
      }
      if(isAssigned == 0){
        $$ = lang_TVar($1,NULL, NORMAL_VAR);
      }
    }
  | QUEST IDENT 
    { $$ = lang_TVar($2, NULL, PATTERN_VAR);}
  | LOWER_NULL
    { $$ = lang_TToken(lang_T_LOWER_NULL); }
  | UPPER_NULL
    { $$ = lang_TToken(lang_T_UPPER_NULL); }

EXPR1 : 
    EXPR0 
    { $$ = $1; }
  | EXPR1 LBRACKET EXPR_ARITH RBRACKET
    { $$ = lang_TArrinx($1, $3);}
  | EXPR1 DOT LPAREN NAME RPAREN
    { $$ = lang_TBinOp(lang_T_FIELDOF, $1, $4);}
  | EXPR1 DOT NAME
    { $$ = lang_TBinOp(lang_T_FIELDOF, $1, $3);} 
  | LPAREN EXPR RPAREN 
    { $$ = $2; }

EXPR_TOP : 
    IDENT MINUSGREATER EXPR1 
    { $$ = lang_TBinOp(lang_T_FIELDOFPTR,lang_TVar($1, NULL, NORMAL_VAR),$3);}
  | EXPR_PREDS
    { $$ = $1;}

EXPR_PREDS :
    EXPR_BOOLEAM 
    { $$ = $1; }
  | EXPR_SEP 
    { $$ = $1; }
  | EXPR_PREDS OR EXPR_BOOLEAM
    { $$ = lang_TBinOp(lang_T_OR, $1, $3);}
  | EXPR_PREDS OR EXPR_SEP
    { $$ = lang_TBinOp(lang_T_OR, $1, $3);} 

EXPR_BOOLEAM : 
    EXPR_ARITH
    { $$ = $1; }
  | EXPR_ARITH EQ EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_EQ, $1, $3);}
  | EXPR_ARITH NEQ EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_NEQ, $1, $3);}
  | EXPR_ARITH LE EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_LE, $1, $3);}
  | EXPR_ARITH GE EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_GE, $1, $3);}
  | EXPR_ARITH LT EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_LT, $1, $3);}
  | EXPR_ARITH GT EXPR_ARITH 
    { $$ = lang_TBinOp(lang_T_GT, $1, $3);}   

EXPR_ARITH : 
    EXPR_MultDiv
    { $$ = $1; }
  | EXPR_ARITH PLUS EXPR_MultDiv
    { $$ = lang_TBinOp(lang_T_ADD,$1, $3);}
  | EXPR_ARITH MINUS EXPR_MultDiv 
    { $$ = lang_TBinOp(lang_T_SUB,$1, $3);}
    
EXPR_MultDiv : 
    EXPR_Uop
    { $$ = $1; }
  | EXPR_MultDiv MULT EXPR_BASE 
    { $$ = lang_TBinOp(lang_T_MUL, $1, $3);}
  | EXPR_MultDiv DIV EXPR_BASE 
    { $$ = lang_TBinOp(lang_T_DIV, $1, $3);}

EXPR_Uop : 
    EXPR_BASE 
    { $$ = $1; }
  | MINUS EXPR_Uop
    { $$ = lang_TUnOp(lang_T_MINUS,$2);}

EXPR_BASE:
    EXPR_FUNC 
    { $$ = $1; }
  | EXPR1 
    { $$ = $1; }

NAME_S :
    IDENT
    { $$ = $1;}
  | ID 
    { $$ = "id";}
  | PRIO 
    { $$ = "priority";}
  | LEFT 
    { $$ = "left";}
  | RIGHT 
    { $$ = "right";} 
  | CHECK 
    { $$ = "check";}
  | ACTION 
    { $$ = "action";}

NAME :
    NAME_S
    { $$ = lang_TVar($1, NULL, NORMAL_VAR);}

EXPR_FUNC :
    EXPR1 LPAREN EXPRS RPAREN
    { $$ = lang_TFunc($1, NULL,$3); }
  | EXPR1 LBRACES POLYTYPES RBRACES LPAREN EXPRS RPAREN
    { $$ = lang_TFunc($1,$3,$6); }
  | EXPR1 LPAREN RPAREN
    { $$ = lang_TFunc($1,NULL,lang_PLNil()); }
  | EXPR1 LBRACES POLYTYPES RBRACES LPAREN RPAREN
    { $$ = lang_TFunc($1,$3,lang_PLNil()); }
  | EXPR1 LBRACES POLYTYPES RBRACES
    { $$ = lang_TFunc($1,$3,lang_PLNil()); }
  | FIELDADDR LPAREN EXPR_ARITH COMMA NAME COMMA NAME RPAREN
    { $$ = lang_TFunc(lang_TVar("field_addr", NULL, NORMAL_VAR), NULL, lang_PLCons($3,lang_PLCons($5, lang_PLCons($7, lang_PLNil())))); }
  | SIZEOF LPAREN CType RPAREN
    { $$ = lang_TSizeof($3); }
  | IDENT COLON POLYTYPE
    { 
      isAssigned = 0;
      if(flag_exist !=0){
        if(isExistVar(&evars,$1)==1){
          $$ = lang_TVar($1,$3, EXISTS_VAR);
          isAssigned = 1;
        }
      }
      if(flag_atom != 0 ){
        if(isExistVar(&svars,$1)==1){
          $$ = lang_TVar($1,$3, ATOM_VAR);
          isAssigned = 1;
        }
      }
      if(isAssigned == 0){
        $$ = lang_TVar($1,$3, NORMAL_VAR);
      }
    }
  | QUEST IDENT COLON POLYTYPE
    { $$ = lang_TVar($2, $4, PATTERN_VAR);}

EXPR_SEP : 
    DATA_AT LPAREN EXPR_ARITH COMMA CType COMMA EXPR_ARITH RPAREN
    { $$ = lang_TDataAt($3, $5, $7);}
  | UNDEF_DATA_AT LPAREN EXPR_ARITH COMMA CType RPAREN
    { $$ = lang_TUndefDataAt($3, $5);}
  | DATA_AT LPAREN EXPR_ARITH COMMA CType_IDENT COMMA EXPR_ARITH RPAREN
    { $$ = lang_TDataAt($3, $5, $7);}
  | UNDEF_DATA_AT LPAREN EXPR_ARITH COMMA CType_IDENT RPAREN
    { $$ = lang_TUndefDataAt($3, $5);}

CType_IDENT:
    IDENT 
    { $$ = initPatternCTypeVar($1);}
  | QUEST IDENT 
    { $$ = initPatternCTypeVar($2);}
  | LPAREN CType_IDENT RPAREN
    { $$ = $2; } 

CType :
    Basic_Ctype
    { $$ = $1; }
  | PTR LPAREN CType RPAREN 
    { $$ = initPatternCTypePtr($3);}

Basic_Ctype:
    PT_VOID
      { $$ = initPatternCTypeVoid(); }
  | PT_CHAR
      { $$ = initPatternCTypeI8(Signed); }
  | PT_UNSIGNED PT_CHAR
      { $$ = initPatternCTypeI8(Unsigned); }
  | I8
      { $$ = initPatternCTypeI8(Signed); }
  | U8
      { $$ = initPatternCTypeI8(Unsigned); }
  | PT_INT
      { $$ = initPatternCTypeI32(Signed); }
  | PT_UNSIGNED PT_INT
      { $$ = initPatternCTypeI32(Unsigned); }
  | I16 
      { $$ = initPatternCTypeI16(Signed); }
  | U16 
      { $$ = initPatternCTypeI16(Unsigned); }
  | I32
      { $$ = initPatternCTypeI32(Signed); }
  | U32
      { $$ = initPatternCTypeI32(Unsigned); }   
  | PT_LONG PT_LONG
      { $$ = initPatternCTypeI64(Signed); } 
  | PT_UNSIGNED PT_LONG PT_LONG
      { $$ = initPatternCTypeI64(Unsigned); }
  | I64
      { $$ = initPatternCTypeI64(Signed); } 
  | U64
      { $$ = initPatternCTypeI64(Unsigned); }
  | PT_STRUCT NAME_S
      { $$ = initPatternCTypeStruct($2); }
  | PT_UNION NAME_S
      { $$ = initPatternCTypeUnion($2); }
  | PT_ENUM NAME_S
      { $$ = initPatternCTypeEnum($2); }

POLYTYPE_BASE:
    LPAREN POLYTYPE RPAREN
    { $$ = $2; }
  | NAME_S
    { $$ = AlterPatternPolyTypeVar($1); }
  | QUEST NAME_S 
    { $$ = initPatternPolyTypeVar($2); }
  | LT NAME_S GT 
    { $$ = AlterPatternPolyTypeConst($2); }
  | NAME_S LBRACES POLYTYPES RBRACES
    { $$ = initPatternPolyTypeApp($1,$3); }
  
POLYTYPE:
    POLYTYPE_BASE
    { $$ = $1; }
  | POLYTYPE_BASE MINUSGREATER POLYTYPE
    { $$ = initPatternPolyTypeArrow($1,$3); }

POLYTYPES:
    POLYTYPE
    { $$ = initPatternPolyTypeList($1,NULL); }
  | POLYTYPE COMMA POLYTYPES
    { $$ = initPatternPolyTypeList($1,$3); }

%%

void llerror(char *s)
{
    fprintf(stderr,"strategy parser: %s around line %d\nGet text : \"%s\"\n",s, llget_lineno() + 1, lltext);
    exit(1);
}

void addVar(struct var_list **vars,char *name){
    struct var_list *p = (struct var_list *)malloc(sizeof(struct var_list));
    if(!p){
        fprintf(stderr,"Unable to malloc memory for new var_list node.");
        exit(1);
    }
    p->var = malloc(strlen(name)+1);
    if(!(p->var)){
        fprintf(stderr,"Unable to malloc memory for new var_list data.");
        exit(1);
    }
    strcpy(p->var,name);
    p->tail = *vars;
    *vars = p;
}

int isExistVar(struct var_list **vars,char *name){
    struct var_list *p = *vars;
    int flag = 0;
    while(p!=NULL){
        if(p->var!=NULL){
            if(!strcmp(p->var,name)){
              flag = 1;
            }
        }
        p = p->tail;
    }
    return flag;
}

void clearVarList(struct var_list **vars){
    struct var_list *p =*vars;
    struct var_list *next =NULL;
    while(p!=NULL){
        next = p->tail;
        free(p->var);
        free(p);
        p = next;
    }
    *vars = NULL;
}