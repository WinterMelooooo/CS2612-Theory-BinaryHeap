#include "utils.h"
#include "env.h"
#include "parser.h"
#include "lexer.h"
#include "plang.h"
#include "../SymExec/Paras.h"

void *__current_scanner = NULL;
char *__current_file = NULL;

void parse_program(FILE *fp, void (*k)(struct partial_program *, struct environment *), struct environment *env) {
  void *scanner, *old_scanner = __current_scanner;
  yypstate *ps;
  YYSTYPE *lval;
  int tok;

  yylex_init(&scanner);
  *(FILE **)((char *)scanner + 8) = fp;
  __current_scanner = scanner;
  lval = (YYSTYPE *)malloc(sizeof(YYSTYPE));
  ps = yypstate_new();
  do {
    tok = yylex(lval, scanner, env);
    if (tok == 0)
      break;
    yypush_parse(ps, tok, lval, NULL, k, env);
  } while (1);
  yypstate_delete(ps);
  yylex_destroy(scanner);
  free(lval);
  __current_scanner = old_scanner;
}

void parse_program_path(char *path, void (*k)(struct partial_program *, struct environment *), struct environment *env) {
  void *scanner, *old_scanner = __current_scanner;
  char *old_file = __current_file;
  yypstate *ps;
  YYSTYPE *lval;
  int tok;

  FILE *fp = fopen(path, "r");
  if (!fp)
    failwith("No such file. %s\n", path);
  yylex_init(&scanner);
  *(FILE **)((char *)scanner + 8) = fp;
  __current_scanner = scanner;
  __current_file = clone_str(path);
  lval = (YYSTYPE *) malloc(sizeof(YYSTYPE));
  ps = yypstate_new();
  do {
    tok = yylex(lval, scanner, env);
    if (tok == 0)
      break;
    yypush_parse(ps, tok, lval, path, k, env);
  } while (1);
  yypstate_delete(ps);
  yylex_destroy(scanner);
  free(lval);
  fclose(fp);
  __current_scanner = old_scanner;
  __current_file = old_file;
}
