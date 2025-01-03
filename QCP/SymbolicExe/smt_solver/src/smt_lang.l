%option noyywrap yylineno
%option outfile="smt_lang_flex.c" header-file="smt_lang_flex.h"
%{
#include "smt_lang.tab.h"
#include "smt_lang.h"
%}

%%
"TT" {
    yylval.b = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
    return PTT;
}

"FF" {
    yylval.b = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
    return PFF;
}

"NOT" {
    return PNOT;
}

"AND"|"/\\" {
    return PAND;
}

"OR"|"\\/" {
    return POR;
}

"IFF"|"<->" {
    return PIFF;
}

"IMPLY"|"->" {
    return PIMPLY;
}

[A-Za-z_]+[0-9A-Za-z_]* {
    char* tmp = (char*)malloc((yyleng+1) * sizeof(char));
    memset(tmp, 0, (yyleng+1) * sizeof(char));
    for(int i = 0; i < yyleng; i++){
        tmp[i] = yytext[i];
    }
    yylval.s = tmp;
    return TVAR;
}

[0-9]+ {
    int num = atoi(yytext);
    yylval.n = num;
    return TNUM;
}

"(" {
    return LB1L;
}

")" {
    return LB1R;
}

"+" {
    return TADD;
}

"-" {
    return TMINUS;
}

"*" {
    return TMULT;
}

"/" {
    return TDIV;
}

">=" {
    return RGE;
}

"<=" {
    return RLE;
}

">" {
    return RGT;
}

"<" {
    return RLT;
}

"=" {
    printf("eq: %s\n", yytext);
    return REQ;
}

"," {
    return COMMA; 
}
[ \t\n\r]    { };

.   {
    printf("%s",yytext);
    yyerror("Mystery Character.");
}

%%