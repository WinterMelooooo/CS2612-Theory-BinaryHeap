#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

#include "LocalMatching.h"
// #include "../Utility/Debugger.h"

// int LocalMatch(struct Assertion * pre, struct Assertion * post) {
//    struct ExistList * exist_list = post->exist_list;
//    struct LocalLinkedHashMap * pre_local_list = pre->local_list, * post_local_list = post->local_list;
//    struct LocalLinkedHashMapNode * pre_local = pre_local_list->head, * post_local = post_local_list->head;

//    while (post_local != NULL) {
//       int key = post_local->id;
//       struct LocalLinkedHashMapVarStack * post_stack = post_local->stack;
//       while (post_stack != NULL) {
//          int post_id = post_stack->id;
//          struct ExprVal * post_expr = post_stack->value;
//          struct ExprVal * pre_expr = LocalFind(key, post_id, pre_local_list);
//          if (pre_expr == NULL) {
//             return 0;
//          } else if (ExprValCheckEqual(pre_expr, post_expr)) {
//             post_stack = post_stack->next;
//             continue;  
//          } else {
//             struct Proposition * new_prop = malloc(sizeof(struct Proposition));
//             new_prop->t = T_PROP_COMPARE;
//             new_prop->d.COMPARE.op = PROP_EQ;
//             new_prop->d.COMPARE.expr1 = ExprValDeepCopy(pre_expr);
//             new_prop->d.COMPARE.expr2 = ExprValDeepCopy(post_expr);
//             post->prop_list = PropListCons(new_prop, post->prop_list);
//          }
//          post_stack = post_stack->next;
//       }
//       post_local = post_local->next;
//    }
//    return 1;
// }
