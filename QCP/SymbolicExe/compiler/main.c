#include "parser_driver.h"
#include "plang.h"
#include "ptrans.h"
#include "utils.h"

struct environment myenv;
extern struct StringList *all_strategy_libs;
struct func_info *finalize_func_def(struct func_info *f, struct environment *env);

void print_func(void *name, void *func_info) {
  (void)name;
  struct func_info *info = func_info;
  {
    print_space();
    print_type(info->ret_type, info->name);
    printf("(");
    struct prog_var_info_list *i;
    for (i = info->param; i != NULL && i->tail != NULL; i = i->tail) {
      print_type(i->head->type, i->head->name);
      printf(", ");
    }
    if (i != NULL)
      print_type(i->head->type, i->head->name);
    printf(")\n");
  }
  {
    struct func_spec *i;
    for (i = info->spec; i != NULL; i = i->next) {
      printf("/ **** function spec ****\n");
      nspace += 2;
      print_spec(i, &myenv.persist);
      nspace -= 2;
      printf(" ****  function spec end  ****/\n");
    }
  }
  if (info->defined) {
    print_space();
    printf("{\n");
    nspace += 2;
    print_cmd(info->body, 1, &myenv.persist);
    nspace -= 2;
    printf("}\n");
  } else
    printf(";\n");
  /* finalize_func_def(info, &env); */
}

#include "../SymExec/Utility/PSstmtPrinter.h"

void dummy_func_handler(struct func_info *_, struct environment *__) {
  (void)_;
  (void)__;
}
void dummy_ps_handler(struct PartialStmt *_, struct environment *__) {
  // PrintPartialStmt(_, &myenv);
  (void)_;
  (void)__;
}

void main_handler(struct partial_program *p, struct environment *env) {
  print_partial_program(p);
  trans(p, env, dummy_func_handler, dummy_ps_handler, dummy_func_handler);
  free_partial_program(p);
}

/* #include <time.h> */

int main() {
  /* struct timespec begin, end; */
  /* clock_gettime(CLOCK_REALTIME, &begin); */
  all_strategy_libs = StringListNil();
  init_env(&myenv);
  parse_program(stdin, main_handler, &myenv);
  /* clock_gettime(CLOCK_REALTIME, &end); */
  /* long nanosec = (end.tv_sec - begin.tv_sec) * 1e9 + end.tv_nsec - begin.tv_nsec; */
  /* printf("%f ms elapsed\n", (double)nanosec / 1000000); */
  hashtbl_iter(&myenv.persist.func, print_func);
}

