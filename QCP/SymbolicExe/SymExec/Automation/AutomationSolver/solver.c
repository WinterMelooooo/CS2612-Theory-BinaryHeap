#include "solver.h"

static void search(struct Assertion * pre, struct Assertion * post, struct StrategyLib * lib,
                   struct intMapping * left_exist_mapping, struct intMapping * right_exist_mapping, struct environment * env) {

    struct ExistList * exist_head = post->exist_list;
    while (exist_head != NULL) {
        intMappingInsert(exist_head->id, initExprValMappingValue(NULL, 0), right_exist_mapping);
        exist_head = exist_head->next;
    }
    while (1) {
        if (!matchStrategyLib(lib, pre, post, left_exist_mapping, right_exist_mapping, env)) break;
    }
}

struct EntailRetType * solve(struct Assertion * pre, struct Assertion * post, struct StrategyLib * lib, struct environment * env) {
    // if (!LocalMatch(pre, post)) return NULL;
    if (exec_info) {
    puts("---------------------------------------------------------------------------------------------");
    puts("Goal:");
    PrintAsrt(pre, env);
    puts("|--");
    PrintAsrt(post, env);
    }
    struct intMapping * left_exist_mapping = initIntMapping(),
                      * right_exist_mapping = initIntMapping();
    search(pre, post, lib, left_exist_mapping, right_exist_mapping, env);
    struct EntailRetType * ret = CreateEntailRetType(CreateAsrt(), IntListNil(), NULL, NewWitness());
    if (exec_info) {
    puts("After applying strategies:");
    PrintAsrt(pre, env);
    puts("|--");
    PrintAsrt(post, env);
    printf("left_added:\n");
    }
    struct intMappingNode * head = left_exist_mapping->head;
    while (head != NULL) {
        if (exec_info) {
          printf("%d ", head->id);
          PrintExprVal(head->val->val, env);
          puts("");
        }
        ret->introed_vars = IntListCons(head->id, ret->introed_vars);
        head = head->next;
    }
    finiIntMapping(left_exist_mapping);
    if (exec_info) {
    printf("exist_mapping:\n");
    }
    ret->ex_instance = create_hashtbl(hash_int, int_equal);
    head = right_exist_mapping->head;
    while (head != NULL) {
        if (exec_info) {
          printf("%d -> ", head->id);
          PrintExprVal(head->val->val, env);
          puts("");
        }
        hashtbl_add(ret->ex_instance, (void *)head->id, ExprValDeepCopy(head->val->val));
        head = head->next;
    }
    finiIntMapping(right_exist_mapping);
    
    return ret;
}

// struct EntailRetType * list_solve(struct Assertion * pre, struct Assertion * post, struct environment * env) {
//     struct StrategyLib * lib = initStrategyLib();
//     addPureStrategies(lib);
//     addListStrategies(lib);
//     struct EntailRetType * ret = solve(pre, post, lib, env);
//     finiStrategyLib(lib);
//     return ret;
// }