%{
	// this part is copied to the beginning of the parser 
	#include "smt_lang.h"
	#include <stdio.h>
	#include "smt_lang_flex.h"
	void yyerror(char*);
	int yylex(void);
	SmtProp *root;
%}

%union {
    int n;
    char* s;
    struct SmtTerm* a;
    struct SmtProp* b;
    void * none;
}

%token <none> LB1L LB1R COMMA

%token <s> TVAR 

%token <n> TNUM 

%token <none> TADD TMULT TDIV TMINUS

%token <none> RLE RLT RGE RGT REQ

%token <none> PAND POR PIFF PIMPLY PNOT

%token <b> PTT PFF

%type <a> EXPR
%type <b> PROP

%left TMINUS TADD
%left TMULT TDIV
%left PAND POR PIFF PIMPLY
%left PNOT
%%

PROP: PTT {
        printf("->PROP\n");
        $$ = $1;
        root = $$;
    }
    | PFF {
        printf("->PROP\n");
        $$ = $1;
        root = $$;
    }
    | LB1L PROP LB1R {
        printf("->PROP\n");
        $$ = $2;
        root = $$;
    }
    | PNOT PROP {
        printf("->PROP\n");
        $$ = newSmtProp(SMTU_PROP, SMTPROP_NOT, $2, NULL, NULL, NULL, true);
        root = $$;
    }
    | PROP PAND PROP {
        printf("->PROP\n");
        $$ = newSmtProp(SMTB_PROP, SMTPROP_AND, $1, $3, NULL, NULL, true);
        root = $$;
    }
    | PROP POR PROP {
        printf("->PROP\n");
        $$ = newSmtProp(SMTB_PROP, SMTPROP_OR, $1, $3, NULL, NULL, true);
        root = $$;
    }
    | PROP PIFF PROP {
        printf("->PROP\n");
        $$ = newSmtProp(SMTB_PROP, SMTPROP_IFF, $1, $3, NULL, NULL, true);
        root = $$;
    }
    | PROP PIMPLY PROP {
        printf("->PROP\n");
        $$ = newSmtProp(SMTB_PROP, SMTPROP_IMPLY, $1, $3, NULL, NULL, true);
        root = $$;
    }
    | EXPR REQ EXPR {
        printf("->PROP\n");
        $$ = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, $1, $3, true);
        root = $$;
    }
    | EXPR RGE EXPR {
        printf("->PROP\n");
        $$ = newSmtProp(SMTAT_PROP_LIA, SMT_GE, NULL, NULL, $1, $3, true);
        root = $$;
    }
    | EXPR RGT EXPR {
        printf("->PROP\n");
        $$ = newSmtProp(SMTAT_PROP_LIA, SMT_GT, NULL, NULL, $1, $3, true);
        root = $$;
    }
    | EXPR RLE EXPR {
        printf("->PROP\n");
        $$ = newSmtProp(SMTAT_PROP_LIA, SMT_LE, NULL, NULL, $1, $3, true);
        root = $$;
    }
    | EXPR RLT EXPR {
        printf("->PROP\n");
        $$ = newSmtProp(SMTAT_PROP_LIA, SMT_LT, NULL, NULL, $1, $3, true);
        root = $$;
    }
;

EXPR: 
    TVAR {
        printf("->EXPR TVAR\n");
        $$ = newSmtTerm(SMT_VarName, 0, 0, $1, NULL, NULL, NULL);
    }
    |TNUM {
        printf("->EXPR TNUM\n");
        $$ = newSmtTerm(SMT_ConstNum, 0, $1, NULL, NULL, NULL, NULL);
    }
    |LB1L EXPR LB1R {
        printf("->EXPR\n");
        $$ = $2;
    }
    |EXPR TADD EXPR {
        printf("->EXPR\n");
        $$ = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, $1, $3);
    }
    |EXPR TMINUS EXPR {
        printf("->EXPR\n");
        $$ = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, $1, $3);
    }
    |TMINUS EXPR {
        printf("->EXPR\n");
        $$ = newSmtTerm(SMT_LiaUTerm, LIA_NEG, 0, NULL, NULL, $2, NULL);
    }
    |EXPR TMULT EXPR {
        printf("->EXPR\n");
        $$ = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, $1, $3);
    }
    |EXPR TDIV EXPR {
        printf("->EXPR\n");
        $$ = newSmtTerm(SMT_LiaBTerm, LIA_DIV, 0, NULL, NULL, $1, $3);
    }
    |TVAR LB1L EXPR LB1R {
        printf("->EXPR\n");
        UFunction* tmp = newUFunction($1, 1, $3, NULL, NULL);
        $$ = newSmtTerm(SMT_UFTerm, 0, 0, NULL, tmp, NULL, NULL);
    }
    |TVAR LB1L EXPR COMMA EXPR LB1R {
        printf("->EXPR\n");
        UFunction* tmp = newUFunction($1, 2, $3, $5, NULL);
         $$ = newSmtTerm(SMT_UFTerm, 0, 0, NULL, tmp, NULL, NULL);
    }
    |TVAR LB1L EXPR COMMA EXPR COMMA EXPR LB1R {
        printf("->EXPR\n");
        UFunction* tmp = newUFunction($1, 3, $3, $5, $7);
         $$ = newSmtTerm(SMT_UFTerm, 0, 0, NULL, tmp, NULL, NULL);
    }
;

%%

void yyerror(char* s)
{
    fprintf(stderr , "%s\n",s);
}