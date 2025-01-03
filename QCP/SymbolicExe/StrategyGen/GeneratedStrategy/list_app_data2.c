#include "verification_stdlib.h"
#include "verification_list.h"
#include "list_app_data2.h"

struct list {
    int head;
    int data;
    struct list *tail;
};

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t, *u;
    if (x == (struct list *) 0) {
        return y;
    } else {
        t = x;
        u = t->tail;
        /*@ Inv exists v w,
            data_at(field_addr(t, head), v) *
            data_at(field_addr(t, data), w) *
            data_at(field_addr(t, tail), u) * 
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        return x;
    }
}