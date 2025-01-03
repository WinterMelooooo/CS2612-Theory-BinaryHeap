#ifndef LEXER_H
#define LEXER_H

#include "parser.h"
#include "env.h"

int yylex_init (void ** scanner);
int yylex(YYSTYPE * yylval_param , void *yyscanner, struct environment *env);
int yyget_lineno (void * yyscanner);
int yyget_column  ( void * yyscanner );
void yyset_lineno (int  _line_number , void * yyscanner);
void yyset_column (int  _column_no , void * yyscanner);
void yyerror(char *, void *k, struct environment *, char *);
int yylex_destroy  (void * yyscanner);

#endif
